include "protocol.dfy"

// The document store. One bucket holds the documents and the timeout keys.
// A missing document is the empty origin. A write of a document that owes a
// deadline is accepted only when the timeout it names is already stored, at
// or before that deadline. The timeout the last accepted write named stays
// while the document still owes one.

module Bucket {
  import opened Network
  import opened Protocol
  import Keys
  import Temp

  function CoverOf(docs: map<string, Temp.Doc>, keys: seq<string>): set<Clock>
    decreases |keys|
  {
    if |keys| == 0 then {}
    else
      var rest := CoverOf(docs, keys[1..]);
      if keys[0] in docs then
        match Temp.Nearest(docs[keys[0]])
        case None => rest
        case Some(d) => rest + {Due(keys[0], d, 0, 0)}
      else rest
  }

  function AnchorOf(docs: map<string, Temp.Doc>, keys: seq<string>): map<string, Clock>
    decreases |keys|
  {
    if |keys| == 0 then map[]
    else
      var rest := AnchorOf(docs, keys[1..]);
      if keys[0] in docs then
        match Temp.Nearest(docs[keys[0]])
        case None => rest
        case Some(d) => rest[keys[0] := Due(keys[0], d, 0, 0)]
      else rest
  }

  function BootTimeouts(docs: map<string, Temp.Doc>): set<Clock> {
    CoverOf(docs, Keys.Sorted(docs.Keys))
  }

  function BootAnchor(docs: map<string, Temp.Doc>): map<string, Clock> {
    AnchorOf(docs, Keys.Sorted(docs.Keys))
  }

  predicate Accept(s: State, key: string, doc: Temp.Doc, cover: Temp.Opt<Clock>)
    requires s.AtBucket?
  {
    match Temp.Nearest(doc)
    case None => true
    case Some(d) =>
      && cover.Some?
      && (cover.Some? ==> cover.value in s.timeouts && cover.value.key == key && cover.value.at <= d)
  }

  predicate LiveAnchor(s: State, t: Clock)
    requires s.AtBucket?
  {
    && t.key in s.docs && t.key in s.anchor && s.anchor[t.key] == t
    && (t.key in s.docs ==> Temp.Nearest(s.docs[t.key]).Some?)
  }

  function step(self: Pid, s: State, i: Input<Pid, Msg>, now: nat): Result<Pid, Msg, State>
  {
    if self.Bucket? && s.AtBucket? then
      match i {
        case Request(from, req) =>
          match req {
            case Req(_, Get(id)) =>
              var key := DocKey(id);
              Result(s, [Answer(from, req, Got(id, DocumentAt(s.docs, id), VersionOf(s.ver, key)))], Keep)
            case Req(_, PutTimeout(id, clock)) =>
              Result(AtBucket(s.docs, s.ver, s.timeouts + {clock}, s.anchor),
                     [Answer(from, req, TimeoutPut(id, clock))], Keep)
            case Req(_, WriteDoc(id, key, doc, version, cover)) =>
              if VersionOf(s.ver, key) == version && Accept(s, key, doc, cover) then
                var anchor' :=
                  match (Temp.Nearest(doc), cover)
                  case (None, _) => s.anchor - {key}
                  case (Some(_), Some(clock)) => s.anchor[key := clock]
                  case (Some(_), None) => s.anchor;
                Result(AtBucket(s.docs[key := doc], s.ver[key := version + 1], s.timeouts, anchor'),
                       [Answer(from, req, DocWrote(id, key))], Keep)
              else
                Result(s, [Answer(from, req, DocRejected(id))], Keep)
            case Req(_, DropTimeout(id, clock)) =>
              if LiveAnchor(s, clock) then
                Result(s, [Answer(from, req, TimeoutDropped(id, clock))], Keep)
              else
                Result(AtBucket(s.docs, s.ver, s.timeouts - {clock}, s.anchor),
                       [Answer(from, req, TimeoutDropped(id, clock))], Keep)
            case _ =>
              Result(s, [], Keep)
          }
        case _ =>
          Result(s, [], Keep)
      }
    else Result(s, [], Keep)
  }
}
