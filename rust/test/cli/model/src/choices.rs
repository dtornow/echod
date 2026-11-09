use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

#[derive(Clone, Debug, Default)]
pub struct Tried(Rc<RefCell<HashMap<&'static str, usize>>>);

impl Tried {
    fn count(&self, label: &str) -> usize {
        self.0.borrow().get(label).copied().unwrap_or(0)
    }
}

#[derive(Clone, Debug)]
pub struct Choices {
    rng: u64,
    tried: Option<Tried>,
}

impl Choices {
    pub fn random(seed: u64) -> Self {
        Choices {
            rng: seed.wrapping_mul(0x9e37_79b9_7f4a_7c15) | 1,
            tried: None,
        }
    }

    pub fn learning(mut self, tried: &Tried) -> Self {
        self.tried = Some(tried.clone());
        self
    }

    pub fn pick(&mut self, n: usize) -> usize {
        assert!(n > 0, "a choice among no alternatives");
        if n == 1 { 0 } else { self.draw(n) }
    }

    pub fn pick_labeled(&mut self, labels: &[&'static str]) -> usize {
        assert!(!labels.is_empty(), "a choice among no alternatives");
        let index = match self.tried.clone() {
            Some(tried) => {
                let least = labels.iter().map(|label| tried.count(label)).min().unwrap();
                let candidates: Vec<usize> = labels
                    .iter()
                    .enumerate()
                    .filter_map(|(i, label)| (tried.count(label) == least).then_some(i))
                    .collect();
                candidates[self.draw(candidates.len())]
            }
            None => self.pick(labels.len()),
        };
        if let Some(tried) = &self.tried {
            *tried.0.borrow_mut().entry(labels[index]).or_default() += 1;
        }
        index
    }

    fn draw(&mut self, n: usize) -> usize {
        self.rng ^= self.rng << 13;
        self.rng ^= self.rng >> 7;
        self.rng ^= self.rng << 17;
        (self.rng % n as u64) as usize
    }
}
