/-
Copyright (c) 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/
module

public import BatteriesKMP.String
public import BatteriesKMP.List.Lemmas
import all Init.Data.String.Substring -- for unfolding `Substring.Raw.isEmpty`

public section

open Std.Stream Array List

namespace Substring.Raw

/-- The substring of `s.str` that ends where the stream `s` starts and has byte size `n`. -/
@[expose] def endingAt (s : Substring.Raw) (n : Nat) : Substring.Raw :=
  { s with startPos := ⟨s.startPos.byteIdx - n⟩, stopPos := s.startPos }

theorem toList_eq_nil_iff {s : Substring.Raw} : Finite.toList s = [] ↔ s.isEmpty = true := by
  match h : Std.Stream.next? s with
  | none =>
    rw [Finite.toList_none h]
    simp only [Std.Stream.next?] at h
    split at h
    · contradiction
    · simp [isEmpty, bsize, String.Pos.Raw.lt_iff] at *; omega
  | some (x, t) =>
    rw [Finite.toList_some h]
    simp only [Std.Stream.next?] at h
    split at h
    · simp [isEmpty, bsize, String.Pos.Raw.lt_iff] at *; omega
    · contradiction

end Substring.Raw

namespace String.Matcher

@[simp] theorem table_ofSubstring (p : Substring.Raw) :
    (ofSubstring p).table = mkPrefixTable (Finite.toList p).toArray :=
  mkPrefixTableOfStream_eq p

@[simp] theorem pattern_ofSubstring (p : Substring.Raw) : (ofSubstring p).pattern = p := rfl

@[simp] theorem state_ofSubstring (p : Substring.Raw) : (ofSubstring p).state.val = 0 := rfl

@[simp] theorem pattern_table_ofSubstring (p : Substring.Raw) :
    (ofSubstring p).table.pattern = Finite.toList p := by
  rw [table_ofSubstring, PrefixTable.pattern_mkPrefixTable, List.toList_toArray]

theorem size_table_ofSubstring (p : Substring.Raw) :
    (ofSubstring p).table.size = (Finite.toList p).length := by
  rw [← PrefixTable.length_pattern, pattern_table_ofSubstring]

theorem findAll_loop_toList (m : Matcher) (s₀ : Substring.Raw) (am : Array.Matcher Char)
    (ht : am.table.IsValid) (pre : List Char) (t : Substring.Raw)
    (hl : Finite.toList s₀ = pre ++ Finite.toList t)
    (hd : ∀ n, Std.Stream.drop s₀ (pre.length + n) = Std.Stream.drop t n)
    (hk : IsLongestPrefixSuffix am.table.pattern pre am.table.size am.state)
    (occs : Array Substring.Raw) :
    (findAll.loop m t am occs).toList = occs.toList ++
      ((List.range' (pre.length + 1) (Finite.toList t).length).filter
        fun j => am.table.pattern.isSuffixOf ((Finite.toList s₀).take j)).map
        fun j => (Std.Stream.drop s₀ j).endingAt m.patternSize := by
  have hiff : ∀ i ≤ (Finite.toList t).length,
      am.table.pattern.isSuffixOf ((Finite.toList s₀).take (pre.length + i)) = true ↔
        (am.run am.state ((Finite.toList t).take i)).val = am.table.size := by
    intro i _
    rw [hl, List.take_append, List.take_of_length_le (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
      isSuffixOf_iff_suffix]
    exact (PrefixTable.foldl_step_isLongestPrefixSuffix ht hk _).eq_iff_suffix
      am.table.length_pattern.symm |>.symm
  rw [findAll.loop]
  split
  · next h =>
    have hn := Array.Matcher.next?_eq_none h
    suffices hnil : (List.range' (pre.length + 1) (Finite.toList t).length).filter
        (fun j => am.table.pattern.isSuffixOf ((Finite.toList s₀).take j)) = [] by
      simp [hnil]
    rw [List.filter_eq_nil_iff]
    intro j hj
    rw [List.mem_range'_1] at hj
    obtain ⟨i, rfl⟩ : ∃ i, j = pre.length + i := ⟨j - pre.length, by omega⟩
    rw [hiff i (by omega)]
    exact hn i (by omega) (by omega)
  · next t' am' h =>
    obtain ⟨xs, hne, hr, rfl, hacc, hmin⟩ := Array.Matcher.next?_eq_some h
    have hrest := hr.toList (s := t) (t := t')
    have hk' := PrefixTable.foldl_step_isLongestPrefixSuffix ht hk xs
    have ih := findAll_loop_toList m s₀ { am with state := am.run am.state xs } ht
      (pre ++ xs) t' (by rw [hl, hrest, List.append_assoc])
      (fun n => by rw [List.length_append, Nat.add_assoc, hd, hr.drop]) hk'
    rw [ih]
    obtain ⟨n, hn⟩ : ∃ n, xs.length = n + 1 := by
      cases xs with
      | nil => contradiction
      | cons _ xs => exact ⟨xs.length, rfl⟩
    have hlen : (Finite.toList t).length = n + (1 + (Finite.toList t').length) := by
      rw [hrest, List.length_append]; omega
    have hdrop : Std.Stream.drop s₀ (pre.length + (n + 1)) = t' := by
      rw [hd, ← hn, ← Nat.add_zero xs.length, hr.drop]; rfl
    have hlast : am.table.pattern.isSuffixOf
        ((Finite.toList s₀).take (pre.length + (n + 1))) = true := by
      rw [hiff (n + 1) (by omega), hrest, ← hn, List.take_left]; exact hacc
    have hfirst : (List.range' (pre.length + 1) n).filter
        (fun j => am.table.pattern.isSuffixOf ((Finite.toList s₀).take j)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro j hj
      rw [List.mem_range'_1] at hj
      obtain ⟨i, rfl⟩ : ∃ i, j = pre.length + i := ⟨j - pre.length, by omega⟩
      rw [hiff i (by omega), hrest, List.take_append_of_le_length (by omega)]
      exact hmin i (by omega) (by omega)
    rw [hlen, ← List.range'_append, ← List.range'_append, List.filter_append,
      List.filter_append, hfirst]
    simp only [List.length_append, hn]
    have e1 : pre.length + 1 + 1 * n = pre.length + (n + 1) := by omega
    have e2 : pre.length + (n + 1) + 1 * 1 = pre.length + (n + 1) + 1 := by omega
    rw [e1, e2, List.range'_one, List.filter_cons]
    simp [hlast, hdrop, Substring.Raw.endingAt]
termination_by t.bsize
decreasing_by exact Array.Matcher.next?_substring_bsize_lt h

theorem findAll_boundaries_toList (m : Matcher) (s₀ t : Substring.Raw) (k : Nat)
    (hd : ∀ n, Std.Stream.drop s₀ (k + n) = Std.Stream.drop t n) (occs : Array Substring.Raw) :
    (findAll.boundaries t occs).toList = occs.toList ++
      (List.range' k ((Finite.toList t).length + 1)).map
        fun j => (Std.Stream.drop s₀ j).endingAt 0 := by
  have h0 : Std.Stream.drop s₀ k = t := hd 0
  rw [findAll.boundaries]
  split
  · next h =>
    rw [Finite.toList_none h]
    simp [h0, Substring.Raw.endingAt]
  · next x t' h =>
    have : Std.Stream.Finite t' := .ofSome h
    have hd' : ∀ n, Std.Stream.drop s₀ (k + 1 + n) = Std.Stream.drop t' n := by
      intro n
      rw [show k + 1 + n = k + (n + 1) by omega, hd, Std.Stream.drop, h]
    rw [findAll_boundaries_toList m s₀ t' (k + 1) hd', Finite.toList_some h, List.length_cons,
      List.range'_succ (s := k), List.map_cons, h0]
    simp [Substring.Raw.endingAt]
termination_by Finite.wrap t

/--
`findAll` returns all occurrences of the pattern `p` in `s`, in order: one for each `j` such that
the first `j` characters of `s` end with the characters of `p`. The occurrence is the substring of
`s.str` of byte size `p.bsize` ending where `s` would start after dropping `j` characters.
-/
theorem findAll_ofSubstring (p s : Substring.Raw) :
    ((ofSubstring p).findAll s).toList =
      ((List.range ((Finite.toList s).length + 1)).filter
        fun j => (Finite.toList p).isSuffixOf ((Finite.toList s).take j)).map
        fun j => (Std.Stream.drop s j).endingAt p.bsize := by
  by_cases hp : p.isEmpty
  · have hp' := Substring.Raw.toList_eq_nil_iff.2 hp
    have hb : p.bsize = 0 := by simpa [Substring.Raw.isEmpty] using hp
    simp only [findAll, pattern_ofSubstring, hp, ↓reduceIte, hp', hb]
    rw [findAll_boundaries_toList (ofSubstring p) s s 0 (by simp) #[], List.range_eq_range']
    simp [List.filter_eq_self.2]
  · have hp' := mt Substring.Raw.toList_eq_nil_iff.1 hp
    have h0 : IsLongestPrefixSuffix (ofSubstring p).table.pattern [] (ofSubstring p).table.size
        (ofSubstring p).state := by
      have := isLongestPrefixSuffix_nil (ofSubstring p).table.pattern
      rwa [PrefixTable.length_pattern, ← state_ofSubstring p] at this
    have := findAll_loop_toList (ofSubstring p) s (ofSubstring p).toMatcher
      (by rw [table_ofSubstring]; exact PrefixTable.isValid_mkPrefixTable _) [] s rfl
      (by simp) h0 #[]
    simp only [findAll, pattern_ofSubstring, hp, Bool.false_eq_true, ↓reduceIte]
    rw [this, List.range_eq_range', List.range'_succ, pattern_table_ofSubstring]
    cases h : Finite.toList p with
    | nil => contradiction
    | cons => simp [patternSize]

theorem findAll_loop_toList_eq (m : Matcher) (t : Substring.Raw) (am : Array.Matcher Char)
    (occs : Array Substring.Raw) :
    (findAll.loop m t am occs).toList = occs.toList ++ (findAll.loop m t am #[]).toList := by
  rw [findAll.loop, findAll.loop]
  split
  · simp
  · next t' am' h =>
    rw [findAll_loop_toList_eq m t' am' (occs.push _), findAll_loop_toList_eq m t' am' (#[].push _)]
    simp
termination_by t.bsize
decreasing_by all_goals (apply Array.Matcher.next?_substring_bsize_lt; assumption)

theorem find?_eq_head?_findAll (m : Matcher) (s : Substring.Raw) :
    m.find? s = (m.findAll s).toList.head? := by
  simp only [find?, findAll]
  split
  · rw [findAll_boundaries_toList m s s 0 (by simp) #[]]
    simp [List.range'_succ, Substring.Raw.endingAt, Std.Stream.drop]
  · rw [findAll.loop]
    split <;> split
    · rfl
    · next h₁ _ _ h₂ => rw [h₁] at h₂; contradiction
    · next h₁ h₂ => rw [h₁] at h₂; contradiction
    · next h₁ _ _ h₂ =>
      rw [h₁] at h₂
      cases h₂
      rw [findAll_loop_toList_eq]
      simp [patternSize]

/--
`find?` returns the first occurrence of the pattern `p` in `s`: the least `j` such that the first
`j` characters of `s` end with the characters of `p`.
-/
theorem find?_ofSubstring (p s : Substring.Raw) :
    (ofSubstring p).find? s =
      ((List.range ((Finite.toList s).length + 1)).find?
        fun j => (Finite.toList p).isSuffixOf ((Finite.toList s).take j)).map
        fun j => (Std.Stream.drop s j).endingAt p.bsize := by
  rw [find?_eq_head?_findAll, findAll_ofSubstring, head?_map, head?_filter]

end String.Matcher

namespace Substring.Raw

theorem findAllSubstr_toList (s p : Substring.Raw) :
    (s.findAllSubstr p).toList =
      ((List.range ((Finite.toList s).length + 1)).filter
        fun j => (Finite.toList p).isSuffixOf ((Finite.toList s).take j)).map
        fun j => (Std.Stream.drop s j).endingAt p.bsize :=
  String.Matcher.findAll_ofSubstring p s

theorem findSubstr?_eq (s p : Substring.Raw) :
    s.findSubstr? p =
      ((List.range ((Finite.toList s).length + 1)).find?
        fun j => (Finite.toList p).isSuffixOf ((Finite.toList s).take j)).map
        fun j => (Std.Stream.drop s j).endingAt p.bsize :=
  String.Matcher.find?_ofSubstring p s

/-- `containsSubstr` decides whether the characters of `p` occur contiguously in `s`. -/
@[simp] theorem containsSubstr_iff {s p : Substring.Raw} :
    s.containsSubstr p ↔ Finite.toList p <:+: Finite.toList s := by
  simp only [containsSubstr, findSubstr?_eq, Option.isSome_map, List.find?_isSome, List.mem_range,
    isSuffixOf_iff_suffix, List.infix_iff_exists_suffix_take]
  constructor
  · rintro ⟨j, hj, h⟩; exact ⟨j, by omega, h⟩
  · rintro ⟨j, hj, h⟩; exact ⟨j, by omega, h⟩

end Substring.Raw
