import BatteriesKMP.String

/-! # Tests for the Knuth-Morris-Pratt (KMP) string matchers -/

/-- Matcher for pattern "abba" -/
def m := String.Matcher.ofString "abba"

#guard ! Option.isSome (m.find? "AbbabbA")

#guard Option.isSome (m.find? "aabbaa")

#guard Array.size (m.findAll "abbabba") = 2

#guard Array.size (m.findAll "abbabbabba") = 3

#guard Option.isSome ("xyyxx".findInfix? "xy")

#guard ! Option.isSome ("xyyxx".findInfix? "xyx")

#guard Array.size ("xyyxx".findAllInfix "xyx") = 0

#guard Array.size ("xyyxxyx".findAllInfix "xyx") = 1

#guard Array.size ("xyxyyxxyx".findAllInfix "xyx") = 2

#guard Array.size ("xyxyxyyxxyxyx".findAllInfix "xyx") = 4

/-! ### Empty patterns match at every character boundary -/

#guard ("".findInfix? "").map (·.startInclusive.offset.byteIdx) == some 0
#guard ("abc".findInfix? "").map (·.startInclusive.offset.byteIdx) == some 0
#guard ("".findAllInfix "").map (·.startInclusive.offset.byteIdx) == #[0]
#guard ("abc".findAllInfix "").map (·.startInclusive.offset.byteIdx) == #[0, 1, 2, 3]
#guard ("aé".findAllInfix "").map (·.startInclusive.offset.byteIdx) == #[0, 1, 3]
#guard ("abc".findAllInfix "").all (·.isEmpty)
#guard ("".toSlice.containsInfix "")
#guard ("".findInfix? "a").isNone

/-! ### Matches are slices of the input -/

#guard ("xyxyyxxyx".findAllInfix "xyx").map (·.copy) == #["xyx", "xyx"]
#guard ("aéb aéb".findAllInfix "éb").map (·.startInclusive.offset.byteIdx) == #[1, 6]
#guard ("aéb aéb".findInfix? "éb").map (·.copy) == some "éb"
