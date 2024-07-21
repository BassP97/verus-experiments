use vstd::prelude::*;

/*
Given an array of integers nums and an integer target, return indices of the two numbers such that they add up to target.

You may assume that each input would have exactly one solution, and you may not use the same element twice.

You can return the answer in any order.
*/
verus! {

    mod two_sum_module {
        use vstd::prelude::*;
        use std::collections::BTreeSet;

        #[verifier::external_fn_specification]
        fn addElement(set: &mut BTreeSet<u32>, element: u32) -> (res: Set<int>)
        ensures
            res == set![element as int]
        {
            set.insert(element);
            set![element as int]
        }

        #[verifier::external_fn_specification]
        fn containsElement(set: &mut BTreeSet<u32>, element: u32, ghostSet: Set<int>) -> (res: bool)
        ensures
            res <==> ghostSet.contains(element as int)
        {
            #[verifier::external_fn_specification]
            set.contains(&element)
        }

        fn two_sum(s: Vec<u32>, target:u32) -> (res: bool)
        requires
            forall|i: int| 0 <= i < s.len() ==> 0 < s[i] < 100000000, // overflow? better way of doing this?
            0 < target < 100000000,
        ensures
            exists|x: int, y: int| s[x] + s[y] == target <==> res
        {
            let mut seen: BTreeSet<u32> = BTreeSet::new(); 
            let mut found_sum = false;
            let n = s.len();
            let mut idx = 0;

            let seenGhostSet: Set<int> =  Set::empty();
            while idx < n
                invariant
                    idx <= n,
                    exists|x: int| seenGhostSet.contains(x) && x + s[idx as int] == target <==> found_sum
            {
                let elem = s[idx];
                let lookingFor = target - elem;
                if (seen.contains(&lookingFor)){
                    found_sum = true;
                }
                let singletonGhostElemSet: Set<int> = addElement(&mut seen, elem);
                proof {
                    seenGhostSet = seenGhostSet + singletonGhostElemSet;
                    assert(seenGhostSet.contains(elem as int));
                }
                idx -= 1;
            }
            found_sum
        }
    }

fn main() {

}

} // verus!
