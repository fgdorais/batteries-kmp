import BatteriesKMP.List

/-! # Tests for the Knuth-Morris-Pratt (KMP) list matchers -/

def lm := List.Matcher.ofList [0,1,1,0]

#guard lm.find? [2,1,1,0,1,1,2] == none

#guard lm.find? [0,0,1,1,0,0] == some (1, 5)

#guard (lm.findAll [0,1,1,0,1,1,0]).size == 2

#guard (lm.findAll [0,1,1,0,1,1,0,1,1,0]).size == 3

/-! ### Empty patterns match at every boundary -/

#guard ([] : List Nat).findInfix? [] == some (0, 0)
#guard [1, 2, 3].findInfix? [] == some (0, 0)
#guard ([] : List Nat).findAllInfix [] == #[(0, 0)]
#guard [1, 2, 3].findAllInfix [] == #[(0, 0), (1, 1), (2, 2), (3, 3)]
#guard ([] : List Nat).containsInfix []
#guard ([] : List Nat).findInfix? [1] == none
#guard [1, 2, 1].findAllInfix [1] == #[(0, 1), (2, 3)]
