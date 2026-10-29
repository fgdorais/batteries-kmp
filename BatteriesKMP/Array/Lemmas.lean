/-
Copyright (c) 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/
module

public import BatteriesKMP.Array
public import BatteriesKMP.List.Lemmas

public section

open Std.Stream

theorem Subarray.next?_toList (s : Subarray α) :
    Stream.next? s.toList = (Stream.next? s).map fun (x, t) => (x, t.toList) := by
  have h1 := s.start_le_stop
  have h2 := s.stop_le_array_size
  show Stream.next? s.toList = (if h : s.start < s.stop then _ else none).map _
  split
  · next h =>
    simp only [Option.map_some, Subarray.toList_eq_drop_take]
    rw [List.drop_eq_getElem_cons (by simp; omega)]
    simp only [List.getElem_take, Array.getElem_toList]
    rfl
  · next h =>
    have : s.toList = [] := by rw [Subarray.toList_eq_drop_take]; simp; omega
    rw [this]; rfl

theorem Subarray.length_toList_eq (s : Subarray α) : s.toList.length = s.stop - s.start := by
  have := s.stop_le_array_size
  simp [Subarray.toList_eq_drop_take]; omega

theorem Std.Stream.Reads.subarray_stop {s t : Subarray α} (h : Reads s xs t) : t.stop = s.stop := by
  induction h with
  | nil => rfl
  | @cons s x s' xs t h _ ih =>
    rw [ih]
    revert h
    show (if h : s.start < s.stop then _ else none) = _ → _
    split
    · intro h; cases h; rfl
    · intro h; cases h

namespace Array

namespace Matcher
open KMP

theorem next?_toList [BEq α] (m : KMP.Matcher α) (s : Subarray α) :
    m.next? s.toList = (m.next? s).map fun (t, m') => (t.toList, m') :=
  KMP.Matcher.next?_map _ Subarray.next?_toList m s

theorem next?_stop [BEq α] {m : KMP.Matcher α} {s t : Subarray α}
    (h : m.next? s = some (t, m')) : t.stop = s.stop := by
  obtain ⟨_, _, hr, -⟩ := KMP.Matcher.next?_eq_some h
  exact hr.subarray_stop

/-- The list matcher with the same automaton and pattern as an array matcher. -/
abbrev toListMatcher (m : Matcher α) : List.Matcher α := { m.toMatcher with pattern := m.pattern.toList }

theorem findAll_loop_eq [BEq α] (m : Matcher α) (xs : Array α) (rest : Subarray α)
    (hs : rest.stop = xs.size) (km : KMP.Matcher α) (occs : Array (Nat × Nat)) :
    findAll.loop m rest km occs =
      List.Matcher.findAll.loop m.toListMatcher xs.toList rest.toList km occs := by
  have hn := next?_toList km rest
  rw [findAll.loop, List.Matcher.findAll.loop]
  split <;> split
  · rfl
  · next h₁ _ _ h₂ => rw [h₁, h₂] at hn; contradiction
  · next h₁ h₂ => rw [h₁, h₂] at hn; contradiction
  · next rest' km' h rest₂ km₂ h₂ =>
    rw [h, h₂] at hn
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hn
    obtain ⟨h1, h2⟩ := hn
    subst h1 h2
    have hs' : rest'.stop = xs.size := by rw [next?_stop h, hs]
    have := rest'.start_le_stop
    have hj : xs.toList.length - rest'.toList.length = rest'.start := by
      rw [Subarray.length_toList_eq, Array.length_toList]; omega
    rw [findAll_loop_eq m xs rest' hs']
    simp only [hj]
termination_by rest.stop - rest.start
decreasing_by exact KMP.Matcher.next?_subarray_lt h

theorem _root_.Array.toList_toSubarray_self (xs : Array α) : xs.toSubarray.toList = xs.toList := by
  simp [Subarray.toList_eq_drop_take, List.take_of_length_le]

theorem findAll_eq [BEq α] (m : Matcher α) (xs : Array α) :
    m.findAll xs = m.toListMatcher.findAll xs.toList := by
  have he : m.pattern.toList.isEmpty = m.pattern.isEmpty := by
    cases m.pattern; simp
  simp only [findAll, List.Matcher.findAll, he, Array.length_toList]
  split
  · rfl
  · rw [findAll_loop_eq m xs xs.toSubarray (by simp) m.toMatcher, Array.toList_toSubarray_self]

theorem find?_eq [BEq α] (m : Matcher α) (xs : Array α) :
    m.find? xs = m.toListMatcher.find? xs.toList := by
  have he : m.pattern.toList.isEmpty = m.pattern.isEmpty := by
    cases m.pattern; simp
  have hn := next?_toList m.toMatcher xs.toSubarray
  rw [Array.toList_toSubarray_self] at hn
  simp only [find?, List.Matcher.find?, he, hn]
  split
  · rfl
  · cases h : m.toMatcher.next? xs.toSubarray with
    | none => rfl
    | some r =>
      obtain ⟨rest, km⟩ := r
      have hs : rest.stop = xs.size := by rw [next?_stop h]; simp
      have := rest.start_le_stop
      have hj : xs.toList.length - rest.toList.length = rest.start := by
        rw [Subarray.length_toList_eq, Array.length_toList]; omega
      simp only [Option.map_some, hj]

theorem toListMatcher_ofArray [BEq α] (p : Array α) :
    (ofArray p).toListMatcher = List.Matcher.ofList p.toList := by
  have ht : mkPrefixTableOfStream p.toList = mkPrefixTable p := by
    rw [mkPrefixTableOfStream_eq, Finite.toList_list, Array.toArray_toList]
  have key : ∀ t t' : PrefixTable α, t = t' →
      ({ table := t, pattern := p.toList } : List.Matcher α) = { table := t', pattern := p.toList } := by
    rintro _ _ rfl; rfl
  exact key _ _ ht.symm

/--
`findAll` returns the start and end positions of all occurrences of the pattern in `xs`, in
increasing order: one for each end position `j` such that `xs.toList.take j` ends with the pattern.
-/
theorem findAll_ofArray [BEq α] [LawfulBEq α] (p xs : Array α) :
    ((ofArray p).findAll xs).toList =
      ((List.range (xs.size + 1)).filter fun j => p.toList.isSuffixOf (xs.toList.take j)).map
        fun j => (j - p.size, j) := by
  rw [findAll_eq, toListMatcher_ofArray, List.Matcher.findAll_ofList]
  simp

/--
`find?` returns the start and end positions of the first occurrence of the pattern in `xs`: the
least end position `j` such that `xs.toList.take j` ends with the pattern.
-/
theorem find?_ofArray [BEq α] [LawfulBEq α] (p xs : Array α) :
    (ofArray p).find? xs =
      ((List.range (xs.size + 1)).find? fun j => p.toList.isSuffixOf (xs.toList.take j)).map
        fun j => (j - p.size, j) := by
  rw [find?_eq, toListMatcher_ofArray, List.Matcher.find?_ofList]
  simp

end Matcher

theorem findInfix?_eq [BEq α] [LawfulBEq α] (xs p : Array α) :
    xs.findInfix? p =
      ((List.range (xs.size + 1)).find? fun j => p.toList.isSuffixOf (xs.toList.take j)).map
        fun j => (j - p.size, j) :=
  Matcher.find?_ofArray p xs

theorem findAllInfix_toList [BEq α] [LawfulBEq α] (xs p : Array α) :
    (xs.findAllInfix p).toList =
      ((List.range (xs.size + 1)).filter fun j => p.toList.isSuffixOf (xs.toList.take j)).map
        fun j => (j - p.size, j) :=
  Matcher.findAll_ofArray p xs

/-- `containsInfix` decides whether the elements of `p` occur contiguously in `xs`. -/
@[simp] theorem containsInfix_iff [BEq α] [LawfulBEq α] {xs p : Array α} :
    xs.containsInfix p ↔ p.toList <:+: xs.toList := by
  have := @List.containsInfix_iff _ _ _ xs.toList p.toList
  rw [List.containsInfix, List.findInfix?_eq, Array.length_toList, Array.length_toList] at this
  rw [containsInfix, findInfix?_eq, ← this]

end Array
