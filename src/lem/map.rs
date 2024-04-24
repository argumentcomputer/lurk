use std::slice::Iter;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Map<K, V>(Vec<(K, V)>);

const LINEAR_SEARCH_MAX: usize = 16;

impl<K: Ord, V> Map<K, V> {
    pub fn from_vec(mut pairs: Vec<(K, V)>) -> Self {
        pairs.sort_unstable_by(|(a, _), (b, _)| a.cmp(b));
        pairs
            .windows(2)
            .for_each(|p| assert!(p[0].0 != p[1].0, "Duplicate pattern found"));
        Self(pairs)
    }

    pub fn to_vec(self) -> Vec<(K, V)> {
        self.0
    }

    pub fn get(&self, f: &K) -> Option<&V> {
        if self.0.len() < LINEAR_SEARCH_MAX {
            self.0.iter().find(|(g, _)| f == g).map(|(_, v)| v)
        } else {
            let t = self.0.binary_search_by(|(g, _)| g.cmp(f)).ok();
            t.map(|i| &self.0[i].1)
        }
    }

    pub fn get_index(&self, i: usize) -> Option<&(K, V)> {
        self.0.get(i)
    }

    pub fn get_index_of(&self, f: &K) -> Option<usize> {
        if self.0.len() < LINEAR_SEARCH_MAX {
            self.0
                .iter()
                .enumerate()
                .find(|(_, (g, _))| f == g)
                .map(|(i, _)| i)
        } else {
            self.0.binary_search_by(|(g, _)| g.cmp(f)).ok()
        }
    }

    pub fn iter(&self) -> Iter<'_, (K, V)> {
        self.0.iter()
    }

    pub fn size(&self) -> usize {
        self.0.len()
    }
}
