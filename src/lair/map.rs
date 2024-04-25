use std::slice::Iter;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Map<K, V>(Vec<(K, V)>);

pub type Set<K> = Map<K, ()>;

const LINEAR_SEARCH_MAX: usize = 16;

impl<K: Ord, V> Map<K, V> {
    pub fn from_vec(mut pairs: Vec<(K, V)>) -> Self {
        pairs.sort_unstable_by(|(a, _), (b, _)| a.cmp(b));
        pairs
            .windows(2)
            .for_each(|p| assert!(p[0].0 != p[1].0, "Duplicate pattern found"));
        Self(pairs)
    }

    pub fn get(&self, f: &K) -> Option<&V> {
        if self.0.len() < LINEAR_SEARCH_MAX {
            self.0.iter().find(|(g, _)| f == g).map(|(_, v)| v)
        } else {
            let t = self.0.binary_search_by(|(g, _)| g.cmp(f)).ok();
            t.map(|i| &self.0[i].1)
        }
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
}

impl<K, V> Map<K, V> {
    #[inline]
    pub fn to_vec(self) -> Vec<(K, V)> {
        self.0
    }

    #[inline]
    pub fn get_index(&self, i: usize) -> Option<&(K, V)> {
        self.0.get(i)
    }

    #[inline]
    pub fn iter(&self) -> Iter<'_, (K, V)> {
        self.0.iter()
    }

    #[inline]
    pub fn size(&self) -> usize {
        self.0.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[should_panic]
    fn test_map_panic() {
        Map::from_vec(vec![("foo", 1), ("foo", 2)]);
    }

    #[test]
    fn test_map_get() {
        let test_with_len = |len| {
            let pairs = (0..len).map(|i| (i, i * i)).collect();
            let map = Map::from_vec(pairs);
            (0..len).for_each(|key| {
                assert_eq!(map.get(&key), Some(key * key).as_ref());
                assert_eq!(map.get_index_of(&key), Some(key));
                assert_eq!(map.get_index(key), Some((key, key * key)).as_ref());
            });
        };

        test_with_len(LINEAR_SEARCH_MAX - 1); // testing linear search
        test_with_len(LINEAR_SEARCH_MAX); // testing binary search
    }
}
