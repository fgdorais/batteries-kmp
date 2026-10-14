import BatteriesKMP.String

/-! # Tests for the Knuth-Morris-Pratt (KMP) string matchers -/

/-- Matcher for pattern "abba" -/
def m := String.Matcher.ofString "abba"

#guard ! Option.isSome (m.find? "AbbabbA")

#guard Option.isSome (m.find? "aabbaa")

#guard Array.size (m.findAll "abbabba") = 2

#guard Array.size (m.findAll "abbabbabba") = 3

#guard Option.isSome ("xyyxx".findSubstr? "xy")

#guard ! Option.isSome ("xyyxx".findSubstr? "xyx")

#guard Array.size ("xyyxx".findAllSubstr "xyx") = 0

#guard Array.size ("xyyxxyx".findAllSubstr "xyx") = 1

#guard Array.size ("xyxyyxxyx".findAllSubstr "xyx") = 2

#guard Array.size ("xyxyxyyxxyxyx".findAllSubstr "xyx") = 4

/-! ### Empty patterns match at every character boundary -/

#guard ("".findSubstr? "").map (·.startInclusive.offset.byteIdx) == some 0
#guard ("abc".findSubstr? "").map (·.startInclusive.offset.byteIdx) == some 0
#guard ("".findAllSubstr "").map (·.startInclusive.offset.byteIdx) == #[0]
#guard ("abc".findAllSubstr "").map (·.startInclusive.offset.byteIdx) == #[0, 1, 2, 3]
#guard ("aé".findAllSubstr "").map (·.startInclusive.offset.byteIdx) == #[0, 1, 3]
#guard ("abc".findAllSubstr "").all (·.isEmpty)
#guard ("".toSlice.containsSubstr "")
#guard ("".findSubstr? "a").isNone

/-! ### Matches are slices of the input -/

#guard ("xyxyyxxyx".findAllSubstr "xyx").map (·.copy) == #["xyx", "xyx"]
#guard ("aéb aéb".findAllSubstr "éb").map (·.startInclusive.offset.byteIdx) == #[1, 6]
#guard ("aéb aéb".findSubstr? "éb").map (·.copy) == some "éb"
