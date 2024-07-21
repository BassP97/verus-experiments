use vstd::prelude::*;

/*
Given an array of integers nums and an integer target, return indices of the two numbers such that they add up to target.

You may assume that each input would have exactly one solution, and you may not use the same element twice.

You can return the answer in any order.
*/
verus! {

    mod two_sum_module {
        use vstd::prelude::*;
        use std::collections::HashSet;

        #[verifier::reject_recursive_types(T)]
        #[verifier::external_body]
        struct ExternalHashSet<T> {
            inner: HashSet<T>,
        }

        #[verifier::external_body]
        impl<T> ExternalHashSet<T> 
        where
            T: std::cmp::Eq + std::hash::Hash + builtin::Integer,
        {
            #[verifier::external_body]
            pub fn new() -> Self {
                ExternalHashSet {
                    inner: HashSet::new(),
                }
            }

            #[verifier::external_body]
            pub fn insert(&mut self, value: T) -> (res: Set<int>)
            ensures
                res == set![value as int]
            {
                self.inner.insert(value);
                return set![value as int];
            }
        
            #[verifier::external_body]
            pub fn contains(&self, value: &T) -> (res: bool)

            {
                self.inner.contains(value)
            }
        }

        fn two_sum(s: Vec<u64>, target:u64) -> (res: bool)
        requires
            forall|i: nat| i < s.len() ==> s[i as int] < 100000000 && s[i as int] > 0 , // overflow? better way of doing this?
            0 < target < 100000000,
        ensures
            exists|x: nat, y: nat| x < s.len() && y < s.len() && s[x as int] + s[y as int] == target <==> res
        {
            let mut seen = ExternalHashSet::new(); 
            let mut found_sum = false;
            let mut idx = 0;

            while idx <  s.len()
                invariant
                    idx <= s.len(),
                    exists|x: int, y: int| x < idx && y < idx && s[x] + s[y] == target <==> found_sum
            {
                let elem = s[idx];
                let lookingFor: u64 = target - elem;
                if (seen.contains(&lookingFor)){
                    found_sum = true;
                }
                idx += 1;
            }
            found_sum
        }
    }

    fn main() {
        
    }
} // verus!
