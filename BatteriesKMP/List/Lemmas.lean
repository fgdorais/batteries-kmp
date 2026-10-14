/-
Copyright (c) 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/
module

public import BatteriesKMP.Array.Lemmas
public import BatteriesKMP.List

public section

namespace List

theorem infix_iff_exists_suffix_take {p l : List α} :
    p <:+: l ↔ ∃ j ≤ l.length, p <:+ l.take j := by
  constructor
  · rintro ⟨s, t, rfl⟩
    refine ⟨(s ++ p).length, by simp, ?_⟩
    rw [List.take_left]
    exact suffix_append _ _
  · rintro ⟨j, -, s, hs⟩
    refine ⟨s, l.drop j, ?_⟩
    rw [hs, List.take_append_drop]

namespace Matcher
open Array

@[simp] theorem table_ofList [BEq α] (p : List α) :
    (ofList p).table = mkPrefixTable p.toArray := rfl

@[simp] theorem pattern_ofList [BEq α] (p : List α) : (ofList p).pattern = p := rfl

@[simp] theorem state_ofList [BEq α] (p : List α) : (ofList p).state.val = 0 := rfl

theorem size_table_ofList [BEq α] [LawfulBEq α] (p : List α) :
    (ofList p).table.size = p.length := by
  rw [← PrefixTable.length_pattern, table_ofList, PrefixTable.pattern_mkPrefixTable,
    List.toList_toArray]

theorem findAll_loop_toList [BEq α] [LawfulBEq α] (m : Matcher α) (ht : m.table.IsValid)
    (xs pre : List α) (k : Fin (m.table.size + 1))
    (hk : IsLongestPrefixSuffix m.table.pattern pre m.table.size k) (occs : Array (Nat × Nat)) :
    (findAll.loop m xs pre.length k occs).toList = occs.toList ++
      ((List.range' (pre.length + 1) xs.length).filter
        fun j => m.table.pattern.isSuffixOf ((pre ++ xs).take j)).map
        fun j => (j - m.table.size, j) := by
  induction xs generalizing pre k occs with
  | nil => simp [findAll.loop]
  | cons x xs ih =>
    have hk' := PrefixTable.step_isLongestPrefixSuffix ht hk x
    have ih' := ih (pre ++ [x]) _ hk'
    simp only [length_append, length_cons, length_nil, Nat.zero_add] at ih'
    rw [findAll.loop, List.length_cons, List.range'_succ, List.filter_cons]
    have htake : (pre ++ x :: xs).take (pre.length + 1) = pre ++ [x] := by
      rw [List.take_append, List.take_of_length_le (by omega)]; simp
    have happ : pre ++ [x] ++ xs = pre ++ x :: xs := by simp
    rw [happ] at ih'
    simp only [htake]
    by_cases hs : m.table.pattern <:+ pre ++ [x]
    · have := (hk'.eq_iff_suffix m.table.length_pattern.symm).2 hs
      simp only [this, ↓reduceIte, isSuffixOf_iff_suffix.2 hs, List.map_cons, ih', Array.toList_push,
        List.append_assoc, List.cons_append, List.nil_append]
    · have := mt (hk'.eq_iff_suffix m.table.length_pattern.symm).1 hs
      simp only [this, ↓reduceIte, (by simpa using hs : ¬ m.table.pattern.isSuffixOf (pre ++ [x]) = true), ih',
        Bool.false_eq_true]

/--
`findAll` returns the start and end positions of all occurrences of the pattern in `l`, in
increasing order: one for each end position `j` such that `l.take j` ends with the pattern.
-/
theorem findAll_ofList [BEq α] [LawfulBEq α] (p l : List α) :
    ((ofList p).findAll l).toList =
      ((List.range (l.length + 1)).filter fun j => p.isSuffixOf (l.take j)).map
        fun j => (j - p.length, j) := by
  have ht := PrefixTable.isValid_mkPrefixTable p.toArray
  have hp : (ofList p).table.pattern = p := by simp
  have hsz := size_table_ofList p
  cases p with
  | nil => simp [findAll, Array.toList_range, List.filter_eq_self.2]
  | cons a p =>
    have h0 : IsLongestPrefixSuffix (ofList (a :: p)).table.pattern [] (ofList (a :: p)).table.size
        (ofList (a :: p)).state := by
      have := isLongestPrefixSuffix_nil (ofList (a :: p)).table.pattern
      rwa [PrefixTable.length_pattern, ← state_ofList (a :: p)] at this
    have := findAll_loop_toList (ofList (a :: p)) ht l [] _ h0 #[]
    simp only [findAll, pattern_ofList, isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
    rw [List.length_nil] at this
    rw [this, hp, hsz, List.range_eq_range', List.range'_succ]
    simp

theorem findAll_loop_toList_eq [BEq α] (m : Matcher α) (xs : List α) (n : Nat)
    (k : Fin (m.table.size + 1)) (occs : Array (Nat × Nat)) :
    (findAll.loop m xs n k occs).toList = occs.toList ++ (findAll.loop m xs n k #[]).toList := by
  induction xs generalizing n k occs with
  | nil => simp [findAll.loop]
  | cons x xs ih =>
    simp only [findAll.loop]
    split
    · rw [ih, ih _ _ (#[].push _)]; simp
    · rw [ih]

theorem find?_loop_eq [BEq α] (m : Matcher α) (xs : List α) (n : Nat)
    (k : Fin (m.table.size + 1)) :
    find?.loop m xs n k = (findAll.loop m xs n k #[]).toList.head? := by
  induction xs generalizing n k with
  | nil => simp [find?.loop, findAll.loop]
  | cons x xs ih =>
    simp only [find?.loop, findAll.loop]
    split
    · rw [findAll_loop_toList_eq]; simp
    · rw [ih]

theorem find?_eq_head?_findAll [BEq α] (m : Matcher α) (l : List α) :
    m.find? l = (m.findAll l).toList.head? := by
  simp only [find?, findAll]
  split
  · simp [Array.toList_range, List.range_succ_eq_map]
  · exact find?_loop_eq ..

/--
`find?` returns the start and end positions of the first occurrence of the pattern in `l`: the
least end position `j` such that `l.take j` ends with the pattern.
-/
theorem find?_ofList [BEq α] [LawfulBEq α] (p l : List α) :
    (ofList p).find? l =
      ((List.range (l.length + 1)).find? fun j => p.isSuffixOf (l.take j)).map
        fun j => (j - p.length, j) := by
  rw [find?_eq_head?_findAll, findAll_ofList, head?_map, head?_filter]

end Matcher

theorem findInfix?_eq [BEq α] [LawfulBEq α] (l p : List α) :
    l.findInfix? p =
      ((List.range (l.length + 1)).find? fun j => p.isSuffixOf (l.take j)).map
        fun j => (j - p.length, j) :=
  Matcher.find?_ofList p l

theorem findAllInfix_toList [BEq α] [LawfulBEq α] (l p : List α) :
    (l.findAllInfix p).toList =
      ((List.range (l.length + 1)).filter fun j => p.isSuffixOf (l.take j)).map
        fun j => (j - p.length, j) :=
  Matcher.findAll_ofList p l

@[simp] theorem containsInfix_iff [BEq α] [LawfulBEq α] {l p : List α} :
    l.containsInfix p ↔ p <:+: l := by
  simp only [containsInfix, findInfix?_eq, Option.isSome_map, find?_isSome, mem_range,
    isSuffixOf_iff_suffix, infix_iff_exists_suffix_take]
  constructor
  · rintro ⟨j, hj, h⟩; exact ⟨j, by omega, h⟩
  · rintro ⟨j, hj, h⟩; exact ⟨j, by omega, h⟩

end List
