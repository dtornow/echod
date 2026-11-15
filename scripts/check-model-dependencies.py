#!/usr/bin/env python3
"""Keep concrete and production crates independent of the abstract model."""
import json
import subprocess
from pathlib import Path

root = Path(__file__).resolve().parent.parent
metadata = json.loads(subprocess.check_output(
    ["cargo", "metadata", "--locked", "--format-version", "1"], cwd=root
))
packages = {p["id"]: p["name"] for p in metadata["packages"]}
nodes = {
    n["id"]: [
        d["pkg"] for d in n["deps"]
        if any(kind["kind"] != "dev" for kind in d["dep_kinds"])
    ]
    for n in metadata["resolve"]["nodes"]
}
guarded = {
    "echod-types", "echod-concrete-spec", "echod-process",
    "echod-runtime", "echod",
}
assert guarded <= set(packages.values()), "guarded package missing from Cargo metadata"
direct = {n["id"]: n["dependencies"] for n in metadata["resolve"]["nodes"]}
for package, name in packages.items():
    if name not in guarded:
        continue
    seen = set()
    pending = list(direct[package])
    while pending:
        dependency = pending.pop()
        if dependency in seen:
            continue
        seen.add(dependency)
        assert not packages[dependency].startswith("echod-abstract-"), (
            f"{name} depends transitively on {packages[dependency]}"
        )
        if name == "echod-types":
            assert packages[dependency] not in {"echod-concrete-spec", "echod-process"}, (
                f"common types depend on model implementation {packages[dependency]}"
            )
        pending.extend(nodes[dependency])
    print(f"{name}: independent of abstract models")
