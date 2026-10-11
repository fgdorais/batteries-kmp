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

#guard ("".findSubstr? "").map (·.startPos.byteIdx) == some 0
#guard ("abc".findSubstr? "").map (·.startPos.byteIdx) == some 0
#guard ("".findAllSubstr "").map (·.startPos.byteIdx) == #[0]
#guard ("abc".findAllSubstr "").map (·.startPos.byteIdx) == #[0, 1, 2, 3]
#guard ("aé".findAllSubstr "").map (·.startPos.byteIdx) == #[0, 1, 3]
#guard ("abc".findAllSubstr "").all (·.isEmpty)
#guard ("".toRawSubstring.containsSubstr "")
#guard ("".findSubstr? "a").isNone
