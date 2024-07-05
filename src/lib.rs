#[allow(dead_code)]
pub mod air;
pub mod lair;
// TODO: unused
// #[allow(dead_code)]
// pub mod logup;
pub mod gadgets;
pub mod lurk;
pub mod poseidon;
pub mod store_core;

pub fn add(left: usize, right: usize) -> usize {
    left + right
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let result = add(2, 2);
        assert_eq!(result, 4);
    }
}
