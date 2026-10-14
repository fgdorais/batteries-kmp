/-
Copyright (c) 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/
module

public import BatteriesKMP.String
public import BatteriesKMP.List.Lemmas

public section

open Std.Stream Array List

namespace String

namespace Slice

variable {s : Slice}

theorem next?_pos_eq_none {p : s.Pos} : Std.Stream.next? p = none ↔ p = s.endPos := by
  simp only [Std.Stream.next?]; split <;> simp_all

theorem next?_pos_eq_some {p q : s.Pos} :
    Std.Stream.next? p = some (x, q) ↔ ∃ h : p ≠ s.endPos, p.get h = x ∧ p.next h = q := by
  simp only [Std.Stream.next?]; split <;> simp_all

theorem Pos.reads_offset {p q : s.Pos} (h : Reads p xs q) :
    q.offset.byteIdx = p.offset.byteIdx + (xs.map Char.utf8Size).sum := by
  induction h with
  | nil => simp
  | @cons p x p' xs q h₁ _ ih =>
    obtain ⟨hp, rfl, rfl⟩ := next?_pos_eq_some.1 h₁
    rw [ih, Pos.byteIdx_offset_next]
    simp [Nat.add_assoc]

theorem Pos.le_of_reads {p q : s.Pos} (h : Reads p xs q) : p ≤ q := by
  rw [Slice.Pos.le_iff, Pos.Raw.le_iff, reads_offset h]
  exact Nat.le_add_right ..

theorem Pos.reads_toList (p : s.Pos) : Reads p (Finite.toList p) s.endPos := by
  match h : Std.Stream.next? p with
  | none =>
    rw [Finite.toList_none h, next?_pos_eq_none.1 h]
    exact .nil _
  | some (x, q) =>
    rw [Finite.toList_some h]
    exact .cons h (reads_toList q)
termination_by Finite.wrap p

theorem utf8ByteSize_eq_sum (s : Slice) :
    s.utf8ByteSize = ((Finite.toList s.startPos).map Char.utf8Size).sum := by
  have := Pos.reads_offset (Pos.reads_toList s.startPos)
  rwa [offset_endPos, byteIdx_rawEndPos, offset_startPos, Pos.Raw.byteIdx_zero,
    Nat.zero_add] at this

theorem utf8ByteSize_eq_zero_iff (s : Slice) :
    s.utf8ByteSize = 0 ↔ Finite.toList s.startPos = [] := by
  rw [utf8ByteSize_eq_sum]
  constructor
  · intro h
    cases hl : Finite.toList s.startPos with
    | nil => rfl
    | cons c l =>
      rw [hl] at h
      have := Char.utf8Size_pos c
      simp at h; omega
  · intro h; simp [h]

theorem pos?_offset (p : s.Pos) : s.pos? p.offset = some p := by
  simp only [pos?, Pos.Raw.isValidForSlice_eq_true_iff.2 p.isValidForSlice, ↓reduceDIte]
  rfl

theorem le_drop (p : s.Pos) (n : Nat) : p ≤ Std.Stream.drop p n := by
  induction n generalizing p with
  | zero => exact Slice.Pos.le_refl _
  | succ n ih =>
    rw [Std.Stream.drop]
    split
    · exact Slice.Pos.le_refl _
    · next q h => exact Slice.Pos.le_trans (Pos.le_of_reads (.cons h (.nil _))) (ih q)

theorem drop_add [Std.Stream σ α] (p : σ) (m n : Nat) :
    Std.Stream.drop p (m + n) = Std.Stream.drop (Std.Stream.drop p m) n := by
  induction m generalizing p with
  | zero => simp [Std.Stream.drop]
  | succ m ih =>
    rw [Nat.add_right_comm, Std.Stream.drop, Std.Stream.drop]
    split
    · cases n <;> simp [Std.Stream.drop, *]
    · exact ih _

theorem drop_le_drop (p : s.Pos) (h : m ≤ n) : Std.Stream.drop p m ≤ Std.Stream.drop p n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [drop_add]; exact le_drop ..

theorem _root_.Std.Stream.Reads.split [Std.Stream σ α] {p t : σ} {A B : List α}
    (h : Reads p (A ++ B) t) : Reads p A (Std.Stream.drop p A.length) ∧
      Reads (Std.Stream.drop p A.length) B t := by
  induction A generalizing p with
  | nil => exact ⟨.nil _, h⟩
  | cons a A ih =>
    cases h with
    | @cons _ _ p' _ _ h₁ h₂ =>
      obtain ⟨ih₁, ih₂⟩ := ih h₂
      have hd : Std.Stream.drop p (a :: A).length = Std.Stream.drop p' A.length := by
        rw [List.length_cons, Std.Stream.drop, h₁]
      rw [hd]
      exact ⟨.cons h₁ ih₁, ih₂⟩

theorem _root_.Std.Stream.Reads.eq_drop [Std.Stream σ α] {p t : σ} (h : Reads p xs t) :
    t = Std.Stream.drop p xs.length := by
  have := h.drop 0; rw [Nat.add_zero] at this; exact this.symm

theorem slice_congr {a a' b b' : s.Pos} {h : a ≤ b} {h' : a' ≤ b'} (ha : a = a') (hb : b = b') :
    s.slice a b h = s.slice a' b' h' := by
  subst ha hb; rfl

end Slice

namespace Matcher
open Slice

@[simp] theorem pattern_ofString (p : Slice) : (ofString p).pattern = p := rfl

@[simp] theorem state_ofString (p : Slice) : (ofString p).state.val = 0 := rfl

theorem table_ofString (p : Slice) :
    (ofString p).table = mkPrefixTable (Finite.toList p.startPos).toArray :=
  mkPrefixTableOfStream_eq p.startPos

@[simp] theorem pattern_table_ofString (p : Slice) :
    (ofString p).table.pattern = Finite.toList p.startPos := by
  rw [table_ofString, PrefixTable.pattern_mkPrefixTable, List.toList_toArray]

theorem isValid_table_ofString (p : Slice) : (ofString p).table.IsValid := by
  rw [table_ofString]; exact PrefixTable.isValid_mkPrefixTable _

theorem sliceEndingAt?_eq (m : Matcher) {s : Slice} {q t : s.Pos} (hr : Reads q P t)
    (hP : m.patternSize = (P.map Char.utf8Size).sum) :
    m.sliceEndingAt? s t = some (s.slice q t (Slice.Pos.le_of_reads hr)) := by
  have ho := Slice.Pos.reads_offset hr
  have hq : (⟨t.offset.byteIdx - m.patternSize⟩ : Pos.Raw) = q.offset := by
    ext; simp only; omega
  rw [sliceEndingAt?, hq, pos?_offset, Option.bind_some]
  simp [Slice.Pos.le_of_reads hr]

/-- The occurrence of a pattern of `n` characters ending after the first `j` characters of `s`. -/
@[expose] def _root_.String.Slice.occurrence (s : Slice) (n j : Nat) : Slice :=
  s.slice (Std.Stream.drop s.startPos (j - n)) (Std.Stream.drop s.startPos j)
    (drop_le_drop _ (Nat.sub_le j n))

theorem findAll_loop_toList (m : Matcher) (s : Slice) (am : Array.Matcher Char)
    (ht : am.table.IsValid)
    (hsz : m.patternSize = (am.table.pattern.map Char.utf8Size).sum)
    (pre : List Char) (t : s.Pos) (hr₀ : Reads s.startPos pre t)
    (hk : IsLongestPrefixSuffix am.table.pattern pre am.table.size am.state)
    (occs : Array Slice) :
    (findAll.loop m s t am occs).toList = occs.toList ++
      ((List.range' (pre.length + 1) (Finite.toList t).length).filter
        fun j => am.table.pattern.isSuffixOf ((Finite.toList s.startPos).take j)).map
        fun j => occurrence s am.table.pattern.length j := by
  have hl := hr₀.toList (s := s.startPos) (t := t)
  have hiff : ∀ i ≤ (Finite.toList t).length,
      am.table.pattern.isSuffixOf ((Finite.toList s.startPos).take (pre.length + i)) = true ↔
        (am.run am.state ((Finite.toList t).take i)).val = am.table.size := by
    intro i _
    rw [hl, List.take_append, List.take_of_length_le (Nat.le_add_right _ _),
      Nat.add_sub_cancel_left, isSuffixOf_iff_suffix]
    exact (PrefixTable.foldl_step_isLongestPrefixSuffix ht hk _).eq_iff_suffix
      am.table.length_pattern.symm |>.symm
  rw [findAll.loop]
  split
  · next h =>
    have hn := Array.Matcher.next?_eq_none h
    suffices hnil : (List.range' (pre.length + 1) (Finite.toList t).length).filter
        (fun j => am.table.pattern.isSuffixOf ((Finite.toList s.startPos).take j)) = [] by
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
    have hr₁ : Reads s.startPos (pre ++ xs) t' := hr₀.append hr
    have ih := findAll_loop_toList m s { am with state := am.run am.state xs } ht hsz
      (pre ++ xs) t' hr₁ hk'
    -- the occurrence found at this step
    have hsuf : am.table.pattern <:+ pre ++ xs :=
      (List.Matcher.run_eq_size_iff ht hk xs).1 hacc
    obtain ⟨A, hA⟩ := hsuf
    have hsplit := (hA ▸ hr₁).split
    have hJ : (pre ++ xs).length - am.table.pattern.length = A.length := by
      rw [← hA, List.length_append]; omega
    have hocc : m.sliceEndingAt? s t' =
        some (occurrence s am.table.pattern.length (pre ++ xs).length) := by
      rw [sliceEndingAt?_eq m hsplit.2 hsz, Slice.occurrence]
      exact congrArg some (slice_congr (by rw [hJ]) hr₁.eq_drop)
    rw [hocc]
    simp only
    rw [ih]
    obtain ⟨n, hn⟩ : ∃ n, xs.length = n + 1 := by
      cases xs with
      | nil => contradiction
      | cons _ xs => exact ⟨xs.length, rfl⟩
    have hlen : (Finite.toList t).length = n + (1 + (Finite.toList t').length) := by
      rw [hrest, List.length_append]; omega
    have hlast : am.table.pattern.isSuffixOf
        ((Finite.toList s.startPos).take (pre.length + (n + 1))) = true := by
      rw [hiff (n + 1) (by omega), hrest, ← hn, List.take_left]; exact hacc
    have hfirst : (List.range' (pre.length + 1) n).filter
        (fun j => am.table.pattern.isSuffixOf ((Finite.toList s.startPos).take j)) = [] := by
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
    simp [hlast]
termination_by s.utf8ByteSize - t.offset.byteIdx
decreasing_by exact Slice.next?_measure_lt h

theorem findAll_boundaries_toList (s : Slice) (pre : List Char) (t : s.Pos)
    (hr₀ : Reads s.startPos pre t) (occs : Array Slice) :
    (findAll.boundaries s t occs).toList = occs.toList ++
      (List.range' pre.length ((Finite.toList t).length + 1)).map (occurrence s 0) := by
  have hocc : s.slice t t (Slice.Pos.le_refl t) = occurrence s 0 pre.length :=
    slice_congr (by rw [Nat.sub_zero]; exact hr₀.eq_drop) hr₀.eq_drop
  rw [findAll.boundaries]
  split
  · next h =>
    rw [Finite.toList_none h]
    simp [hocc]
  · next x t' h =>
    rw [findAll_boundaries_toList s (pre ++ [x]) t' (hr₀.append (.cons h (.nil _))),
      Finite.toList_some h, List.length_cons, List.range'_succ (s := pre.length), List.map_cons,
      ← hocc]
    simp
termination_by s.utf8ByteSize - t.offset.byteIdx
decreasing_by exact Std.Stream.next_of_next?_eq_some ‹Std.Stream.next? t = some _›

/--
`findAll` returns all occurrences of the pattern `p` in `s`, in order: one for each `j` such that
the first `j` characters of `s` end with the characters of `p`. That occurrence is the slice of `s`
between the positions after `j - n` and after `j` characters, where `n` is the number of characters
of `p`.
-/
theorem findAll_ofString (p s : Slice) :
    ((ofString p).findAll s).toList =
      ((List.range ((Finite.toList s.startPos).length + 1)).filter
        fun j => (Finite.toList p.startPos).isSuffixOf ((Finite.toList s.startPos).take j)).map
        (occurrence s (Finite.toList p.startPos).length) := by
  by_cases hp : p.utf8ByteSize = 0
  · have hp' := (Slice.utf8ByteSize_eq_zero_iff p).1 hp
    simp only [findAll, patternSize, pattern_ofString, hp, ↓reduceIte, hp']
    rw [findAll_boundaries_toList s [] s.startPos (.nil _) #[], List.range_eq_range']
    simp [List.filter_eq_self.2]
  · have h0 : IsLongestPrefixSuffix (ofString p).table.pattern [] (ofString p).table.size
        (ofString p).state := by
      have := isLongestPrefixSuffix_nil (ofString p).table.pattern
      rwa [PrefixTable.length_pattern, ← state_ofString p] at this
    have := findAll_loop_toList (ofString p) s (ofString p).toMatcher (isValid_table_ofString p)
      (by rw [pattern_table_ofString, patternSize, pattern_ofString, utf8ByteSize_eq_sum])
      [] s.startPos (.nil _) h0 #[]
    simp only [findAll, patternSize, pattern_ofString, hp, ↓reduceIte]
    rw [this, List.range_eq_range', List.range'_succ, pattern_table_ofString]
    have hp' := mt (Slice.utf8ByteSize_eq_zero_iff p).2 hp
    cases h : Finite.toList p.startPos with
    | nil => contradiction
    | cons => simp

theorem findAll_loop_toList_eq (m : Matcher) (s : Slice) (t : s.Pos) (am : Array.Matcher Char)
    (occs : Array Slice) :
    (findAll.loop m s t am occs).toList = occs.toList ++ (findAll.loop m s t am #[]).toList := by
  rw [findAll.loop, findAll.loop]
  split
  · simp
  · next t' am' h =>
    split
    · rw [findAll_loop_toList_eq m s t' am' (occs.push _),
        findAll_loop_toList_eq m s t' am' (#[].push _)]
      simp
    · rw [findAll_loop_toList_eq m s t' am' occs]
termination_by s.utf8ByteSize - t.offset.byteIdx
decreasing_by all_goals exact Slice.next?_measure_lt ‹_›

theorem find?_loop_of_none {m : Matcher} {s : Slice} {t : s.Pos} {am : Array.Matcher Char}
    (h : am.next? t = none) : find?.loop m s t am = none := by
  rw [find?.loop]; split <;> simp_all

theorem find?_loop_of_some {m : Matcher} {s : Slice} {t t' : s.Pos} {am am' : Array.Matcher Char}
    (h : am.next? t = some (t', am')) : find?.loop m s t am =
      match m.sliceEndingAt? s t' with
      | some r => some r
      | none => find?.loop m s t' am' := by
  rw [find?.loop]; split
  · simp_all
  · next h' => rw [h] at h'; cases h'; rfl

theorem findAll_loop_of_none {m : Matcher} {s : Slice} {t : s.Pos} {am : Array.Matcher Char}
    (h : am.next? t = none) : findAll.loop m s t am occs = occs := by
  rw [findAll.loop]; split <;> simp_all

theorem findAll_loop_of_some {m : Matcher} {s : Slice} {t t' : s.Pos}
    {am am' : Array.Matcher Char} (h : am.next? t = some (t', am')) :
    findAll.loop m s t am occs = findAll.loop m s t' am'
      (match m.sliceEndingAt? s t' with
        | some r => occs.push r
        | none => occs) := by
  rw [findAll.loop]; split
  · simp_all
  · next h' => rw [h] at h'; cases h'; rfl

theorem find?_loop_eq (m : Matcher) (s : Slice) (t : s.Pos) (am : Array.Matcher Char) :
    find?.loop m s t am = (findAll.loop m s t am #[]).toList.head? := by
  match hn : am.next? t with
  | none => rw [find?_loop_of_none hn, findAll_loop_of_none hn]; rfl
  | some (t', am') =>
    have := Slice.next?_measure_lt hn
    rw [find?_loop_of_some hn, findAll_loop_of_some hn]
    split <;> rename_i heq
    · rw [findAll_loop_toList_eq]; simp
    · exact find?_loop_eq m s t' am'
termination_by s.utf8ByteSize - t.offset.byteIdx

theorem find?_eq_head?_findAll (m : Matcher) (s : Slice) :
    m.find? s = (m.findAll s).toList.head? := by
  simp only [find?, findAll]
  split
  · rw [findAll_boundaries_toList s [] s.startPos (.nil _) #[]]
    simp only [List.length_nil, List.range'_succ, List.map_cons]
    simp [Slice.occurrence, Std.Stream.drop]
  · exact find?_loop_eq m s s.startPos _

/--
`find?` returns the first occurrence of the pattern `p` in `s`: the least `j` such that the first
`j` characters of `s` end with the characters of `p`.
-/
theorem find?_ofString (p s : Slice) :
    (ofString p).find? s =
      ((List.range ((Finite.toList s.startPos).length + 1)).find?
        fun j => (Finite.toList p.startPos).isSuffixOf ((Finite.toList s.startPos).take j)).map
        (occurrence s (Finite.toList p.startPos).length) := by
  rw [find?_eq_head?_findAll, findAll_ofString, head?_map, head?_filter]

end Matcher

namespace Slice

theorem findAllInfix_toList (s p : Slice) :
    (s.findAllInfix p).toList =
      ((List.range ((Finite.toList s.startPos).length + 1)).filter
        fun j => (Finite.toList p.startPos).isSuffixOf ((Finite.toList s.startPos).take j)).map
        (occurrence s (Finite.toList p.startPos).length) :=
  String.Matcher.findAll_ofString p s

theorem findInfix?_eq (s p : Slice) :
    s.findInfix? p =
      ((List.range ((Finite.toList s.startPos).length + 1)).find?
        fun j => (Finite.toList p.startPos).isSuffixOf ((Finite.toList s.startPos).take j)).map
        (occurrence s (Finite.toList p.startPos).length) :=
  String.Matcher.find?_ofString p s

/-- `containsInfix` decides whether the characters of `p` occur contiguously in `s`. -/
@[simp] theorem containsInfix_iff {s p : Slice} :
    s.containsInfix p ↔ Finite.toList p.startPos <:+: Finite.toList s.startPos := by
  rw [containsInfix, findInfix?_eq]
  simp only [Option.isSome_map, List.find?_isSome, List.mem_range,
    isSuffixOf_iff_suffix, List.infix_iff_exists_suffix_take]
  constructor
  · rintro ⟨j, hj, h⟩; exact ⟨j, by omega, h⟩
  · rintro ⟨j, hj, h⟩; exact ⟨j, by omega, h⟩

end Slice

end String
