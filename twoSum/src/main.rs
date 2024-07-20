use vstd::prelude::*;

/*
Given an array of integers nums and an integer target, return indices of the two numbers such that they add up to target.

You may assume that each input would have exactly one solution, and you may not use the same element twice.

You can return the answer in any order.
*/
verus! {
    mod M1 {
        use builtin::*;

        pub closed spec fn min(x: i32, y: i32) -> i32 {
            if x <= y {
                x
            } else {
                y
            }
        }

        pub proof fn lemma_min(x: i32, y: i32)
            ensures
                min(x,y) <= x && min(x,y) <= y,
                x < y ==> min(x, y) == x,
                x > y ==> min(x, y) == y,
                x == y ==> min(x, y) == x,
        {}
    }

    mod M2 {
        use builtin::*;
        use crate::M1::*;

        fn test() {
            let x: i32 = 100;
            let y: i32 = x-1;
            proof {
                lemma_min(x,y);
            }
            assert(min(x, y) ==x); // succeeds
        }
    }



fn main() {

}

} // verus!
