import BatteriesKMP.Array

/-! # Tests for the Knuth-Morris-Pratt (KMP) array matchers -/

def am := Array.Matcher.ofArray #[0,1,1,0]

#guard am.find? #[2,1,1,0,1,1,2] == none

#guard am.find? #[0,0,1,1,0,0] == some (1, 5)

#guard (am.findAll #[0,1,1,0,1,1,0]).size == 2

#guard (am.findAll #[0,1,1,0,1,1,0,1,1,0]).size == 3

/-! ### Empty patterns match at every boundary -/

#guard (#[] : Array Nat).findInfix? #[] == some (0, 0)
#guard #[1, 2, 3].findInfix? #[] == some (0, 0)
#guard (#[] : Array Nat).findAllInfix #[] == #[(0, 0)]
#guard #[1, 2, 3].findAllInfix #[] == #[(0, 0), (1, 1), (2, 2), (3, 3)]
#guard (#[] : Array Nat).containsInfix #[]
#guard (#[] : Array Nat).findInfix? #[1] == none
#guard #[1, 2, 1].findAllInfix #[1] == #[(0, 1), (2, 3)]

/-! ### Overlapping matches -/

#guard #[0, 1, 1, 0, 1, 1, 0].findAllInfix #[0, 1, 1, 0] == #[(0, 4), (3, 7)]
#guard !#[2, 1, 1, 0, 1, 1, 2].containsInfix #[0, 1, 1, 0]
