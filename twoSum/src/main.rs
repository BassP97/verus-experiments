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
            (index1 > 0 && nums.len() > 1)
            && (
                (check_pairs_including_num_at_index(nums, target, index1, (nums.len()-1) as nat))
                ||
                contains_two_elements_that_add_to_target(nums, target, (index1-1) as nat)
            )
        }

        fn runtime_sum(val1: u32, val2: u32) -> (res: u32)
        requires
            val1 + val2 <= 200000000
        ensures
            res == val1 + val2 //kinda silly
        {
            return val1 + val2
        }


        fn two_sum(s: Vec<u32>, target:u32) -> (res: bool)
        requires
            s.len() >= 2,
            target < 100000000,
            forall|i: nat| i < s.len() ==> s[i as int] < 100000000 && s[i as int] >= 0 , // overflow? better way of doing this?
            0 < target < 100000000,
        ensures
            res == contains_two_elements_that_add_to_target(s@, target, s@.len())
        {
            let mut seen:Vec<u32> = Vec::new();
            let mut found_sum = false;
            let mut idx = 0;
            let mut looking_for = 0;

            while idx < s.len()
                invariant
                    idx < s.len() ==> s[idx as int] < 100000000,
                    0 < target < 100000000,
                    idx < s.len(),
                    (exists|x: nat, y: nat| x < idx < s.len() && y < idx < s.len() && x != y && s[x as int] + s[y as int] == target) ==> found_sum,
                    forall|x: nat| x < idx < s.len() ==> seen[x as int] == s[x as int]
            {
                looking_for = runtime_sum(target, s[idx]);
                let mut idx2 = 0;
                while idx2 < seen.len()
                invariant
                    s[idx as int] < 100000000,
                    0 < target < 100000000,
                    0 <= idx <= s.len(),
                    (exists|x: nat| seen[x as int] == looking_for) ==> found_sum,
                    idx2 <= seen.len(),
                    looking_for == target + s[idx as int]
                {
                    if seen[idx2] == looking_for {
                        found_sum = true;
                        proof {
                            assert(looking_for == target + s[idx as int]);
                            assert(exists|x: nat, y: nat| x < idx < s.len() && y < idx < s.len() && x != y && (s[x as int] + s[y as int]  == target));
                        }
                    }
                    idx2 += 1
                }
                seen.push(s[idx]);
                idx = idx + 1;
            }
            found_sum
        }

        fn prove_two_sum(){
            proof {
                reveal_with_fuel(contains_two_elements_that_add_to_target, 100);
                reveal_with_fuel(check_pairs_including_num_at_index, 100)
            }
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
