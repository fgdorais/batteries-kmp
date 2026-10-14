/-
Copyright (c) 2023 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/
module

public import BatteriesKMP.Matcher

public section

theorem KMP.Matcher.next?_subarray_lt [BEq α] {m : Matcher α} {s t : Subarray α}
    (h : m.next? s = some (t, m')) : t.stop - t.start < s.stop - s.start := by
  replace h := next?_transGen h
  induction h with
  | single h => exact h
  | tail _ h ih => exact Nat.lt_trans ih h

namespace Array

/-- Knuth-Morris-Pratt matcher type

This type is used to keep data for running the Knuth-Morris-Pratt (KMP) array matching algorithm.
KMP is a linear time algorithm to locate all contiguous subarrays of an array that match a given
pattern. Generating the algorithm data is also linear in the size of the pattern but the data can
be re-used to match the same pattern over multiple arrays.

The KMP data for a pattern can be generated using `Matcher.ofArray`. Then `Matcher.find?` and
`Matcher.findAll` can be used to run the algorithm on an input array.
```
def m := Matcher.ofArray #[0,1,1,0]

#eval Option.isSome <| m.find? #[2,1,1,0,1,1,2] -- false
#eval Option.isSome <| m.find? #[0,0,1,1,0,0] -- true

#eval Array.size <| m.findAll #[0,1,1,0,1,1,0] -- 2
#eval Array.size <| m.findAll #[0,1,1,0,1,1,0,1,1,0] -- 3
```
-/
structure Matcher (α : Type _) extends KMP.Matcher α where
  /-- The pattern for the matcher -/
  pattern : Array α

/-- Make KMP matcher from array pattern. -/
@[inline] def Matcher.ofArray [BEq α] (pattern : Array α) : Matcher α where
  table := KMP.mkPrefixTable pattern
  pattern := pattern

/--
Find all start and end positions of all infix subarrays of `xs` matching `m.pattern`.
The subarrays may be overlapping.
-/
def Matcher.findAll [BEq α] (m : Matcher α) (xs : Array α) : Array (Nat × Nat) :=
  if m.pattern.isEmpty then
    Array.range (xs.size + 1) |>.map fun i => (i, i)
  else
    loop xs.toSubarray m.toMatcher #[]
where
  /-- Accumulator loop for `Array.Matcher.findAll` -/
  loop (rest : Subarray α) (km : KMP.Matcher α) (occs : Array (Nat × Nat)) : Array (Nat × Nat) :=
    match h : km.next? rest with
    | none => occs
    | some (rest', km') =>
      have := KMP.Matcher.next?_subarray_lt h
      let j := rest'.start
      loop rest' km' (occs.push (j - m.table.size, j))
  termination_by rest.stop - rest.start

/--
Find the start and end positions of the first infix subarray of `xs` matching `m.pattern`,
or `none` if there is no such subarray.
-/
def Matcher.find? [BEq α] (m : Matcher α) (xs : Array α) : Option (Nat × Nat) :=
  if m.pattern.isEmpty then
    some (0, 0)
  else
    match m.next? xs.toSubarray with
    | none => none
    | some (rest, _) =>
      let j := rest.start
      some (j - m.table.size, j)

/--
Returns all the start and end positions of all infix subarrays of `xs` that match `pattern`.
The subarrays may be overlapping.
-/
@[inline] def findAllInfix [BEq α] (xs pattern : Array α) : Array (Nat × Nat) :=
  (Matcher.ofArray pattern).findAll xs

/--
Returns the start and end positions of the first infix subarray of `xs` that matches `pattern`,
or `none` if there is no such subarray.
-/
@[inline] def findInfix? [BEq α] (xs pattern : Array α) : Option (Nat × Nat) :=
  (Matcher.ofArray pattern).find? xs

/--
Returns true iff `pattern` occurs as an infix subarray of `xs`.
-/
@[inline] def containsInfix [BEq α] (xs pattern : Array α) : Bool :=
  findInfix? xs pattern |>.isSome

end Array
