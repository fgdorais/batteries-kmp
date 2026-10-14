/-
Copyright (c) 2024 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/
module

public import BatteriesKMP.Matcher

public section

theorem Array.Matcher.next?_list_length_lt [BEq α] {m : Matcher α} {l t : List α}
    (h : m.next? l = some (t, m')) : t.length < l.length := by
  replace h := next?_transGen h
  induction h with
  | single h => exact h
  | tail _ h ih => exact Nat.lt_trans ih h

namespace List

/-- Knuth-Morris-Pratt matcher type

This type is used to keep data for running the Knuth-Morris-Pratt (KMP) list matching algorithm.
KMP is a linear time algorithm to locate all contiguous sublists of a list that match a given
pattern. Generating the algorithm data is also linear in the length of the pattern but the data can
be re-used to match the same pattern over multiple lists.

The KMP data for a pattern can be generated using `Matcher.ofList`. Then `Matcher.find?` and
`Matcher.findAll` can be used to run the algorithm on an input list.
```
def m := Matcher.ofList [0,1,1,0]

#eval Option.isSome <| m.find? [2,1,1,0,1,1,2] -- false
#eval Option.isSome <| m.find? [0,0,1,1,0,0] -- true

#eval Array.size <| m.findAll [0,1,1,0,1,1,0] -- 2
#eval Array.size <| m.findAll [0,1,1,0,1,1,0,1,1,0] -- 3
```
-/
structure Matcher (α : Type _) extends Array.Matcher α where
  /-- The pattern for the matcher -/
  pattern : List α

/-- Make KMP matcher from list pattern. -/
@[inline] def Matcher.ofList [BEq α] (pattern : List α) : Matcher α where
  toMatcher := Array.Matcher.ofStream pattern
  pattern := pattern

/--
Find all start and end positions of all infix sublists of `l` matching `m.pattern`.
The sublists may be overlapping.
-/
def Matcher.findAll [BEq α] (m : Matcher α) (l : List α) : Array (Nat × Nat) :=
  if m.pattern.isEmpty then
    Array.range (l.length + 1) |>.map fun i => (i, i)
  else
    loop l m.toMatcher #[]
where
  /-- Accumulator loop for `List.Matcher.findAll` -/
  loop (rest : List α) (am : Array.Matcher α) (occs : Array (Nat × Nat)) : Array (Nat × Nat) :=
    match h : am.next? rest with
    | none => occs
    | some (rest', am') =>
      have := Array.Matcher.next?_list_length_lt h
      let j := l.length - rest'.length
      loop rest' am' (occs.push (j - m.table.size, j))
  termination_by rest.length

/--
Find the start and end positions of the first infix sublist of `l` matching `m.pattern`,
or `none` if there is no such sublist.
-/
def Matcher.find? [BEq α] (m : Matcher α) (l : List α) : Option (Nat × Nat) :=
  if m.pattern.isEmpty then
    some (0, 0)
  else
    match m.next? l with
    | none => none
    | some (rest, _) =>
      let j := l.length - rest.length
      some (j - m.table.size, j)

/--
Returns all the start and end positions of all infix sublists of `l` that match `pattern`.
The sublists may be overlapping.
-/
@[inline] def findAllInfix [BEq α] (l pattern : List α) : Array (Nat × Nat) :=
  (Matcher.ofList pattern).findAll l

/--
Returns the start and end positions of the first infix sublist of `l` that matches `pattern`,
or `none` if there is no such sublist.
-/
@[inline] def findInfix? [BEq α] (l pattern : List α) : Option (Nat × Nat) :=
  (Matcher.ofList pattern).find? l

/--
Returns true iff `pattern` occurs as an infix sublist of `l`.
-/
@[inline] def containsInfix [BEq α] (l pattern : List α) : Bool :=
  findInfix? l pattern |>.isSome
