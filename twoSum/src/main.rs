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
        spec fn check_pairs_including_num_at_index(nums: Seq<i32>, target: i32, fixed_index: nat, floating_index: nat) -> bool
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

        spec fn contains_two_elements_that_add_to_target(nums: Seq<i32>, target: i32, index1: nat) -> (res: bool)
        decreases index1,
        {
            (index1 > 0 && nums.len() > 1)
            && (
                (check_pairs_including_num_at_index(nums, target, index1, (nums.len()-1) as nat))
                ||
                contains_two_elements_that_add_to_target(nums, target, (index1-1) as nat)
            )
        }

        // fn runtime_sub(val1: i32, val2: i32) -> (res: i32)
        // requires
        //     0 < val1 < 100000000,
        //     0 < val2 < 100000000
        // ensures
        //     res == val1 - val2 //kinda silly
        // {
        //     val1 - val2
        // }


        fn two_sum(s: Vec<i32>, target:i32) -> (res: bool)
        requires
            s.len() >= 2,
            0 < target < 100000000,
            forall|i: nat| i < s@.len() ==> (s@[i as int] < 100000000 && s@[i as int] > 0)
        ensures
            res == contains_two_elements_that_add_to_target(s@, target, s@.len())
        {
            let mut seen:Vec<i32> = Vec::new();
            let mut found_sum = false;
            let mut idx = 0;
            let mut looking_for = 0;

            proof {
                assert(seen@.len() == 0);
            }
            while idx < s.len()
                invariant
                    forall|i: nat| i < s@.len() ==> (s@[i as int] < 100000000 && s@[i as int] > 0),
                    forall|i: nat| i < seen@.len() ==> (seen@[i as int] < 100000000 && seen@[i as int] > 0),
                    0 < target < 100000000,
                    0 <= idx <= s@.len(),
                    seen@.len() <= s@.len(),
                    (exists|x: nat, y: nat| x < idx < s@.len() && y < idx < s@.len() && x != y && s@[x as int] + s@[y as int] == target) ==> found_sum,
                    forall|x: nat| x < idx < s@.len() && x < idx < seen@.len()==> seen@[x as int] == s@[x as int] // TODO: make this an unordered comparison
            {
                looking_for = target - s[idx];
                let mut idx2 = 0;

                while idx2 < seen.len()
                invariant
                    forall|i: nat| i < s@.len() ==> (s@[i as int] < 100000000 && s@[i as int] > 0),
                    forall|i: nat| i < seen@.len() ==> (seen@[i as int] < 100000000 && seen@[i as int] > 0),
                    0 < target < 100000000,

                    seen@.len() <= s@.len(),
                    forall|i: nat| (i < seen@.len() && i < s@.len()) ==> s@[i as int] == seen@[i as int],

                    0 <= idx < s@.len(),
                    0 <= idx2 <= seen@.len(),

                    looking_for == target - s@[idx as int],
                    (exists|x: nat| x < idx2 < seen@.len() && seen@[x as int] == looking_for) ==> found_sum
                {
                    if seen[idx2] == looking_for {
                        found_sum = true;
                        proof {
                            assert(looking_for == target - s@[idx as int]);
                            assert(seen@[idx2 as int] == target - s@[idx as int]);
                        }
                    }
                    idx2 += 1
                }
                seen.push(s[idx]);
                proof {
                    assert(seen@.len() <= s@.len());
                }
                idx = idx + 1;
            }
            found_sum
        }

        fn prove_two_sum(){
            proof {
                reveal_with_fuel(contains_two_elements_that_add_to_target, 100);
                reveal_with_fuel(check_pairs_including_num_at_index, 100)
            }
            let mut v: Vec<i32> = Vec::new();
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
