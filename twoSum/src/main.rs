use vstd::prelude::*;

/*
Given an array of integers nums and an integer target, return true if there exist two ints at different indices that add up to the target

You may assume that each input would have exactly one solution, and you may not use the same element twice.

You can return the answer in any order.
*/
verus! {
    mod two_sum_module {
        use vstd::prelude::*;

        // Inner recursive function to check all pairs
        spec fn check_pairs_including_num_at_index(nums: Seq<u32>, target: u32, fixed_index: nat, floating_index: nat) -> bool
        decreases floating_index
        {
            // Base case: If all pairs are checked
            // case 2, if floating index val plus fixed index val == target, we return
            // case 3, recurse using the next possible floating index val
            floating_index > 0 &&
                (
                    (floating_index != fixed_index && (nums[fixed_index as int] + nums[floating_index as int] == target))
                    ||
                    check_pairs_including_num_at_index(nums, target, fixed_index, (floating_index - 1) as nat)
                )
        }

        spec fn contains_two_elements_that_add_to_target(nums: Seq<u32>, target: u32, index1: nat) -> (res: bool)
        decreases index1,
        {
            (index1 > -1 && nums.len() > 1)
            && (
                (check_pairs_including_num_at_index(nums, target, index1, (nums.len()-1) as nat))
                ||
                contains_two_elements_that_add_to_target(nums, target, (index1-1) as nat)
            )
        }

        fn two_sum(s: Vec<u32>, target:u32) -> (res: bool)
        requires
            forall|i: nat| i < s.len() ==> s[i as int] < 100000000 && s[i as int] >= 0 , // overflow? better way of doing this?
            0 < target < 100000000,
        ensures
            res == contains_two_elements_that_add_to_target(s@, target, s@.len())
        {
            let mut seen:Vec<u32> = Vec::new();
            let mut found_sum = false;
            let mut idx = 0;

            while idx < s.len()
                invariant
                    idx <= s.len(),
                    exists|x: int, y: int| (x < idx && y < idx && && x != y && s[x] + s[y] == target) <==> found_sum,
            {
                let elem = s[idx];
                let lookingFor = target - elem;
                let idx2 = 0;
                while idx2 < seen.len() {
                    if seen[idx2] == lookingFor {
                        found_sum = true;
                    }
                }
                idx += 1;
            }
            found_sum
        }

        fn prove_two_sum(){
            let mut v: Vec<u32> = Vec::new();
            v.push(0);
            v.push(10);
            v.push(20);
            v.push(30);
            v.push(40);
            let val = two_sum(v, 70);
        }

    }

    fn main() {

    }
} // verus!
