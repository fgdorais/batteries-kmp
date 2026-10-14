/-
Copyright (c) 2023 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/
module

public import BatteriesKMP.Array

public section

namespace String.Slice

/-- Stream of the characters of a slice `s`, starting from a position in `s`. -/
instance (s : Slice) : Std.Stream s.Pos Char where
  next? p := if h : p = s.endPos then none else some (p.get h, p.next h)

theorem Pos.byteIdx_offset_le {s : Slice} (p : s.Pos) : p.offset.byteIdx ≤ s.utf8ByteSize :=
  p.isValidForSlice.le_utf8ByteSize

instance (s : Slice) : Std.Stream.WellFounded s.Pos Char :=
  .ofMeasure (fun p => s.utf8ByteSize - p.offset.byteIdx) <| by
    intro p q _ h
    simp only [Std.Stream.next?] at h
    split at h
    · contradiction
    · next hp =>
      cases h
      have := Pos.byteIdx_offset_le (p.next hp)
      rw [Pos.byteIdx_offset_next] at this ⊢
      have := Char.utf8Size_pos (p.get hp)
      omega

theorem next?_measure_lt {s : Slice} {m : Array.Matcher Char} {p q : s.Pos}
    (h : m.next? p = some (q, m')) :
    s.utf8ByteSize - q.offset.byteIdx < s.utf8ByteSize - p.offset.byteIdx := by
  replace h := Array.Matcher.next?_transGen h
  induction h with
  | single h => exact h
  | tail _ h ih => exact Nat.lt_trans ih h

end String.Slice

namespace String

/-- Knuth-Morris-Pratt matcher type

This type is used to keep data for running the Knuth-Morris-Pratt (KMP) string matching algorithm.
KMP is a linear time algorithm to locate all substrings of a string that match a given pattern.
Generating the algorithm data is also linear in the length of the pattern but the data can be
re-used to match the same pattern over different strings.

The KMP data for a pattern string can be generated using `Matcher.ofString`. Then `Matcher.find?`
and `Matcher.findAll` can be used to run the algorithm on an input string.
```
def m := Matcher.ofString "abba"

#eval Option.isSome <| m.find? "AbbabbA" -- false
#eval Option.isSome <| m.find? "aabbaa" -- true

#eval Array.size <| m.findAll "abbabba" -- 2
#eval Array.size <| m.findAll "abbabbabba" -- 3
```
-/
structure Matcher extends Array.Matcher Char where
  /-- The pattern for the matcher -/
  pattern : Slice

/-- Make KMP matcher from pattern slice -/
@[expose, inline] def Matcher.ofSlice (pattern : Slice) : Matcher where
  toMatcher := Array.Matcher.ofStream pattern.startPos
  pattern := pattern

/-- Make KMP matcher from pattern string -/
@[expose, inline] def Matcher.ofString (pattern : String) : Matcher :=
  Matcher.ofSlice pattern

/-- The byte size of the string pattern for the matcher -/
abbrev Matcher.patternSize (m : Matcher) : Nat := m.pattern.utf8ByteSize

/-- The slice of `s` of byte size `m.patternSize` that ends at `stop`, if there is one. -/
@[expose] def Matcher.sliceEndingAt? (m : Matcher) (s : Slice) (stop : s.Pos) : Option Slice :=
  (s.pos? ⟨stop.offset.byteIdx - m.patternSize⟩).bind fun start =>
    if h : start ≤ stop then some (s.slice start stop h) else none

/-- Find all slices of `s` matching `m.pattern`. -/
@[expose] def Matcher.findAll (m : Matcher) (s : Slice) : Array Slice :=
  if m.patternSize = 0 then
    boundaries s.startPos #[]
  else
    loop s.startPos m.toMatcher #[]
where
  /-- Empty slices at every character boundary of `s`, for an empty pattern. -/
  boundaries (p : s.Pos) (occs : Array Slice) : Array Slice :=
    let occs := occs.push (s.slice p p (Slice.Pos.le_refl p))
    match _h : Std.Stream.next? p with
    | none => occs
    | some (_, p) => boundaries p occs
  termination_by s.utf8ByteSize - p.offset.byteIdx
  decreasing_by exact Std.Stream.next_of_next?_eq_some _h
  /-- Accumulator loop for `String.Matcher.findAll` -/
  loop (p : s.Pos) (am : Array.Matcher Char) (occs : Array Slice) : Array Slice :=
    match h : am.next? p with
    | none => occs
    | some (p', am') =>
      have := Slice.next?_measure_lt h
      loop p' am' <| match m.sliceEndingAt? s p' with
        | some r => occs.push r
        | none => occs
  termination_by s.utf8ByteSize - p.offset.byteIdx

/-- Find the first slice of `s` matching `m.pattern`, or `none` if no such slice exists. -/
@[expose] def Matcher.find? (m : Matcher) (s : Slice) : Option Slice :=
  if m.patternSize = 0 then
    some (s.slice s.startPos s.startPos (Slice.Pos.le_refl _))
  else
    loop s.startPos m.toMatcher
where
  /-- Search loop for `String.Matcher.find?` -/
  loop (p : s.Pos) (am : Array.Matcher Char) : Option Slice :=
    match h : am.next? p with
    | none => none
    | some (p', am') =>
      have := Slice.next?_measure_lt h
      match m.sliceEndingAt? s p' with
      | some r => some r
      | none => loop p' am'
  termination_by s.utf8ByteSize - p.offset.byteIdx

end String

namespace String.Slice

/--
Returns all the slices of `s` that match `pattern`.
-/
@[expose, inline] def findAllSubstr (s pattern : Slice) : Array Slice :=
  (String.Matcher.ofSlice pattern).findAll s

/--
Returns the first slice of `s` that matches `pattern`,
or `none` if there is no such slice.
-/
@[expose, inline] def findSubstr? (s pattern : Slice) : Option Slice :=
  (String.Matcher.ofSlice pattern).find? s

/--
Returns true iff `pattern` occurs as a slice of `s`.
-/
@[expose, inline] def containsSubstr (s pattern : Slice) : Bool :=
  s.findSubstr? pattern |>.isSome

end String.Slice

namespace String

@[inherit_doc Slice.findAllSubstr]
abbrev findAllSubstr (s : String) (pattern : Slice) : Array Slice :=
  s.toSlice.findAllSubstr pattern

@[inherit_doc Slice.findSubstr?]
abbrev findSubstr? (s : String) (pattern : Slice) : Option Slice :=
  s.toSlice.findSubstr? pattern

end String
