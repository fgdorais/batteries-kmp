/-
Copyright (c) 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/
module

public import BatteriesKMP.Matcher.Lemmas
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
open KMP Std.Stream

@[simp] theorem table_ofList [BEq α] (p : List α) :
    (ofList p).table = mkPrefixTable p.toArray := by
  simp [ofList, KMP.Matcher.ofStream, mkPrefixTableOfStream_eq]

@[simp] theorem pattern_ofList [BEq α] (p : List α) : (ofList p).pattern = p := rfl

@[simp] theorem state_ofList [BEq α] (p : List α) : (ofList p).state.val = 0 := rfl

theorem isValid_table_ofList [BEq α] [LawfulBEq α] (p : List α) : (ofList p).table.IsValid := by
  rw [table_ofList]; exact PrefixTable.isValid_mkPrefixTable _

@[simp] theorem pattern_table_ofList [BEq α] [LawfulBEq α] (p : List α) :
    (ofList p).table.pattern = p := by
  simp

theorem size_table_ofList [BEq α] [LawfulBEq α] (p : List α) :
    (ofList p).table.size = p.length := by
  rw [← PrefixTable.length_pattern, pattern_table_ofList]

/-- The automaton accepts after reading `ys` exactly when the pattern is a suffix. -/
theorem run_eq_size_iff [BEq α] [LawfulBEq α] {am : KMP.Matcher α} (ht : am.table.IsValid)
    (hk : IsLongestPrefixSuffix am.table.pattern pre am.table.size am.state) (ys : List α) :
    (am.run am.state ys).val = am.table.size ↔ am.table.pattern <:+ pre ++ ys :=
  (PrefixTable.foldl_step_isLongestPrefixSuffix ht hk ys).eq_iff_suffix
    am.table.length_pattern.symm

theorem findAll_loop_toList [BEq α] [LawfulBEq α] (m : Matcher α) (l : List α)
    (am : KMP.Matcher α) (ht : am.table.IsValid) (hsz : am.table.size = m.table.size)
    (pre rest : List α) (hl : l = pre ++ rest)
    (hk : IsLongestPrefixSuffix am.table.pattern pre am.table.size am.state)
    (occs : Array (Nat × Nat)) :
    (findAll.loop m l rest am occs).toList = occs.toList ++
      ((List.range' (pre.length + 1) rest.length).filter
        fun j => am.table.pattern.isSuffixOf (l.take j)).map
        fun j => (j - m.table.size, j) := by
  have htake : ∀ i ≤ rest.length, l.take (pre.length + i) = pre ++ rest.take i := by
    intro i _; simp [hl, List.take_append, List.take_of_length_le (Nat.le_add_right pre.length i)]
  have hiff : ∀ i ≤ rest.length,
      am.table.pattern.isSuffixOf (l.take (pre.length + i)) = true ↔
        (am.run am.state (rest.take i)).val = am.table.size := by
    intro i hi
    rw [htake i hi, isSuffixOf_iff_suffix, run_eq_size_iff ht hk]
  rw [findAll.loop]
  split
  · next h =>
    have hn := KMP.Matcher.next?_eq_none h
    rw [Finite.toList_list] at hn
    suffices hnil : (List.range' (pre.length + 1) rest.length).filter
        (fun j => am.table.pattern.isSuffixOf (l.take j)) = [] by
      simp [hnil]
    rw [List.filter_eq_nil_iff]
    intro j hj
    rw [List.mem_range'_1] at hj
    obtain ⟨i, rfl⟩ : ∃ i, j = pre.length + i := ⟨j - pre.length, by omega⟩
    rw [hiff i (by omega)]
    exact hn i (by omega) (by omega)
  · next rest' am' h =>
    obtain ⟨xs, hne, hr, rfl, hacc, hmin⟩ := KMP.Matcher.next?_eq_some h
    have hrest := hr.list
    have hk' := PrefixTable.foldl_step_isLongestPrefixSuffix ht hk xs
    have ih := findAll_loop_toList m l { am with state := am.run am.state xs } ht hsz
      (pre ++ xs) rest' (by rw [hl, hrest, List.append_assoc]) hk'
    rw [ih]
    obtain ⟨n, hn⟩ : ∃ n, xs.length = n + 1 := by
      cases xs with
      | nil => contradiction
      | cons _ xs => exact ⟨xs.length, rfl⟩
    have hlen : rest.length = n + (1 + rest'.length) := by
      rw [hrest, List.length_append]; omega
    have hj : l.length - rest'.length = pre.length + (n + 1) := by
      rw [hl, hrest]; simp; omega
    have hlast : am.table.pattern.isSuffixOf (l.take (pre.length + (n + 1))) = true := by
      rw [hiff (n + 1) (by omega), hrest, ← hn, List.take_left]; exact hacc
    have hfirst : (List.range' (pre.length + 1) n).filter
        (fun j => am.table.pattern.isSuffixOf (l.take j)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro j hj
      rw [List.mem_range'_1] at hj
      obtain ⟨i, rfl⟩ : ∃ i, j = pre.length + i := ⟨j - pre.length, by omega⟩
      rw [hiff i (by omega), hrest, List.take_append_of_le_length (by omega)]
      exact hmin i (by omega) (by omega)
    rw [hlen, ← List.range'_append, ← List.range'_append, List.filter_append,
      List.filter_append, hfirst, hj]
    simp only [List.length_append, hn]
    have e1 : pre.length + 1 + 1 * n = pre.length + (n + 1) := by omega
    have e2 : pre.length + (n + 1) + 1 * 1 = pre.length + (n + 1) + 1 := by omega
    rw [e1, e2, List.range'_one, List.filter_cons]
    simp [hlast]
termination_by rest.length
decreasing_by exact KMP.Matcher.next?_list_length_lt h

theorem findAll_loop_toList_eq [BEq α] (m : Matcher α) (l rest : List α) (am : KMP.Matcher α)
    (occs : Array (Nat × Nat)) :
    (findAll.loop m l rest am occs).toList =
      occs.toList ++ (findAll.loop m l rest am #[]).toList := by
  rw [findAll.loop, findAll.loop]
  split
  · simp
  · next rest' am' h =>
    rw [findAll_loop_toList_eq m l rest' am' (occs.push _),
      findAll_loop_toList_eq m l rest' am' (#[].push _)]
    simp
termination_by rest.length
decreasing_by all_goals (apply KMP.Matcher.next?_list_length_lt; assumption)

theorem find?_eq_head?_findAll [BEq α] (m : Matcher α) (l : List α) :
    m.find? l = (m.findAll l).toList.head? := by
  simp only [find?, findAll]
  split
  · simp [Array.toList_range, List.range_succ_eq_map]
  · rw [findAll.loop]
    split <;> split
    · rfl
    · next h₁ _ _ h₂ => rw [h₁] at h₂; contradiction
    · next h₁ h₂ => rw [h₁] at h₂; contradiction
    · next rest₁ am₁ h₁ rest₂ am₂ h₂ =>
      rw [h₁] at h₂
      cases h₂
      rw [findAll_loop_toList_eq]
      simp

/--
`findAll` returns the start and end positions of all occurrences of the pattern in `l`, in
increasing order: one for each end position `j` such that `l.take j` ends with the pattern.
-/
theorem findAll_ofList [BEq α] [LawfulBEq α] (p l : List α) :
    ((ofList p).findAll l).toList =
      ((List.range (l.length + 1)).filter fun j => p.isSuffixOf (l.take j)).map
        fun j => (j - p.length, j) := by
  cases p with
  | nil => simp [findAll, Array.toList_range, List.filter_eq_self.2]
  | cons a p =>
    have h0 : IsLongestPrefixSuffix (ofList (a :: p)).table.pattern [] (ofList (a :: p)).table.size
        (ofList (a :: p)).state := by
      have := isLongestPrefixSuffix_nil (ofList (a :: p)).table.pattern
      rwa [PrefixTable.length_pattern, ← state_ofList (a :: p)] at this
    have := findAll_loop_toList (ofList (a :: p)) l (ofList (a :: p)).toMatcher
      (isValid_table_ofList _) rfl [] l rfl h0 #[]
    simp only [findAll, pattern_ofList, isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
    rw [this, List.range_eq_range', List.range'_succ, size_table_ofList]
    simp


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
