/-
Copyright (c) 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/
module

public import BatteriesKMP.Array
public import Batteries.Data.Stream

public section

namespace Std.Stream

/-- `Reads s xs t` holds when reading the values `xs` from the stream `s` leaves the stream `t`. -/
inductive Reads [Stream σ α] : σ → List α → σ → Prop
  /-- Reading nothing leaves the stream unchanged. -/
  | nil (s : σ) : Reads s [] s
  /-- Read one value, then the rest. -/
  | cons : next? s = some (x, s') → Reads s' xs t → Reads s (x :: xs) t

theorem Reads.append [Stream σ α] {s t u : σ} (h₁ : Reads s xs t) (h₂ : Reads t ys u) :
    Reads s (xs ++ ys) u := by
  induction h₁ with
  | nil => exact h₂
  | cons h _ ih => exact .cons h (ih h₂)

theorem Reads.toList [HasNextRelation σ α] {s t : σ} (h : Reads s xs t) :
    ∀ [Stream.Finite s] [Stream.Finite t], Finite.toList s = xs ++ Finite.toList t := by
  induction h with
  | nil => intros; rfl
  | @cons s x s' xs t h₁ _ ih =>
    intros
    have : Stream.Finite s' := .ofSome h₁
    rw [Finite.toList_some h₁, ih, List.cons_append]

theorem Reads.list {l t : List α} (h : Reads l xs t) : l = xs ++ t := by
  induction h with
  | nil => rfl
  | @cons l x l' xs t h₁ _ ih =>
    match l, h₁ with
    | _ :: _, h₁ =>
      simp only [Stream.next?, Option.some.injEq, Prod.mk.injEq] at h₁
      obtain ⟨rfl, rfl⟩ := h₁
      rw [ih, List.cons_append]

theorem Reads.drop [Stream σ α] {s t : σ} (h : Reads s xs t) (n : Nat) :
    Stream.drop s (xs.length + n) = Stream.drop t n := by
  induction h with
  | nil => simp
  | @cons s x s' xs t h₁ _ ih =>
    rw [List.length_cons, Nat.add_right_comm, Stream.drop, h₁]
    exact ih

theorem Finite.foldl_eq_foldl_toList [HasNextRelation σ α] (s : σ) [Stream.Finite s]
    (f : β → α → β) (init : β) : Finite.foldl s f init = (Finite.toList s).foldl f init := by
  match h : next? s with
  | none => rw [Finite.foldl_none h, Finite.toList_none h]; rfl
  | some (x, t) =>
    have : Stream.Finite t := .ofSome h
    rw [Finite.foldl_some h, Finite.toList_some h, List.foldl_cons,
      foldl_eq_foldl_toList t]
termination_by Finite.wrap s

end Std.Stream

namespace List

variable {p s s' : List α}

/--
`IsLongestPrefixSuffix p s bound n` holds when `n` is the largest `j ≤ bound` such that
`p.take j` is a suffix of `s`.
-/
structure IsLongestPrefixSuffix (p s : List α) (bound n : Nat) : Prop where
  /-- The length is within the bound. -/
  le : n ≤ bound
  /-- The prefix of length `n` is a suffix. -/
  suffix : p.take n <:+ s
  /-- No longer prefix within the bound is a suffix. -/
  max : ∀ j ≤ bound, p.take j <:+ s → j ≤ n

theorem IsLongestPrefixSuffix.unique (h₁ : IsLongestPrefixSuffix p s b n₁)
    (h₂ : IsLongestPrefixSuffix p s b n₂) : n₁ = n₂ :=
  Nat.le_antisymm (h₂.max _ h₁.le h₁.suffix) (h₁.max _ h₂.le h₂.suffix)

theorem IsLongestPrefixSuffix.congr (h : ∀ j ≤ b, p.take j <:+ s ↔ p.take j <:+ s')
    (hs : IsLongestPrefixSuffix p s b n) : IsLongestPrefixSuffix p s' b n where
  le := hs.le
  suffix := (h _ hs.le).1 hs.suffix
  max j hj hj' := hs.max j hj ((h _ hj).2 hj')

theorem IsLongestPrefixSuffix.of_take_eq {p p' : List α}
    (h : ∀ j ≤ b, p.take j = p'.take j) (hs : IsLongestPrefixSuffix p s b n) :
    IsLongestPrefixSuffix p' s b n where
  le := hs.le
  suffix := h _ hs.le ▸ hs.suffix
  max j hj hj' := hs.max j hj (h _ hj ▸ hj')

/--
Fallback step of the KMP automaton: if `r` is the longest proper border of `p.take k`, then the
prefixes of `p` of length at most `k` that are suffixes of `p.take k ++ [x]` are the same as those
that are suffixes of `p.take r ++ [x]`.
-/
theorem take_suffix_take_concat_iff_of_border {p : List α} (hk : k ≤ p.length)
    (hr : IsLongestPrefixSuffix p (p.take k) (k - 1) r) (hj : j ≤ k) :
    p.take j <:+ p.take k ++ [x] ↔ p.take j <:+ p.take r ++ [x] := by
  constructor
  · intro h
    match j, hj with
    | 0, _ => simp
    | j + 1, hj =>
      have hjp : j < p.length := by omega
      rw [List.take_succ_eq_append_getElem hjp,
        suffix_append_inj_of_length_eq (s₁ := [p[j]]) (s₂ := [x]) rfl] at h
      rw [List.take_succ_eq_append_getElem hjp,
        suffix_append_inj_of_length_eq (s₁ := [p[j]]) (s₂ := [x]) rfl]
      refine ⟨?_, h.2⟩
      have hjr : j ≤ r := hr.max j (by omega) h.1
      apply suffix_of_suffix_length_le h.1 hr.suffix
      simp only [length_take]
      omega
  · intro h
    apply h.trans
    rw [suffix_append_self_iff]
    exact hr.suffix

theorem length_le_of_take_suffix (hj : j ≤ p.length) (h : p.take j <:+ s) : j ≤ s.length := by
  have := h.length_le
  simp only [length_take] at this
  omega

theorem isLongestPrefixSuffix_nil (p : List α) : IsLongestPrefixSuffix p [] p.length 0 where
  le := Nat.zero_le _
  suffix := by simp
  max j hj h := by
    have := length_le_of_take_suffix hj h
    simp only [length_nil] at this
    omega

theorem IsLongestPrefixSuffix.eq_iff_suffix (h : IsLongestPrefixSuffix p s b n)
    (hb : b = p.length) : n = b ↔ p <:+ s := by
  subst hb
  constructor
  · intro hn
    have := h.suffix
    rwa [hn, take_length] at this
  · intro hs
    have := h.max p.length (Nat.le_refl _) (by rwa [take_length])
    have := h.le
    omega

/--
Transition step of the KMP automaton: if `p.take k` is the longest prefix of `p` that is a suffix
of `s` then the prefixes of `p` that are suffixes of `s ++ [x]` are the same as those that are
suffixes of `p.take k ++ [x]`.
-/
theorem take_suffix_concat_iff_of_isLongestPrefixSuffix
    (h : IsLongestPrefixSuffix p s b k) (hb : p.length ≤ b) (hj : j ≤ p.length) :
    p.take j <:+ s ++ [x] ↔ p.take j <:+ p.take k ++ [x] := by
  constructor
  · intro hs
    match j, hj with
    | 0, _ => simp
    | j + 1, hj =>
      have hjp : j < p.length := by omega
      rw [List.take_succ_eq_append_getElem hjp,
        suffix_append_inj_of_length_eq (s₁ := [p[j]]) (s₂ := [x]) rfl] at hs
      rw [List.take_succ_eq_append_getElem hjp,
        suffix_append_inj_of_length_eq (s₁ := [p[j]]) (s₂ := [x]) rfl]
      refine ⟨?_, hs.2⟩
      have hjk : j ≤ k := h.max j (by omega) hs.1
      apply suffix_of_suffix_length_le hs.1 h.suffix
      simp only [length_take]
      omega
  · intro hs
    apply hs.trans
    rw [suffix_append_self_iff]
    exact h.suffix

theorem isLongestPrefixSuffix_take_succ {p : List α} (hk : k < p.length) :
    IsLongestPrefixSuffix p (p.take k ++ [p[k]]) p.length (k + 1) where
  le := hk
  suffix := by rw [List.take_succ_eq_append_getElem hk]; exact suffix_rfl
  max j hj h := by
    have := length_le_of_take_suffix hj h
    simp only [length_append, length_take, length_cons, length_nil] at this
    omega

theorem le_of_take_suffix_take_concat {p : List α} (hk : k ≤ p.length)
    (hx : ∀ h : k < p.length, p[k] ≠ x) (hj : j ≤ p.length)
    (h : p.take j <:+ p.take k ++ [x]) : j ≤ k := by
  have := length_le_of_take_suffix hj h
  simp only [length_append, length_take, length_cons, length_nil] at this
  if hjk : j = k + 1 then
    subst hjk
    have hk' : k < p.length := by omega
    rw [List.take_succ_eq_append_getElem hk',
      suffix_append_inj_of_length_eq (s₁ := [p[k]]) (s₂ := [x]) rfl] at h
    simp only [cons.injEq, and_true] at h
    exact absurd h.2 (hx hk')
  else
    omega

end List

namespace Array.PrefixTable

/-- The pattern of a prefix table. -/
def pattern (t : PrefixTable α) : List α := t.toArray.toList.map (·.1)

@[simp] theorem length_pattern (t : PrefixTable α) : t.pattern.length = t.size := by
  simp [pattern]

theorem getElem_pattern (t : PrefixTable α) (h : i < t.pattern.length) :
    t.pattern[i] = (t.toArray[i]'(by simpa using h)).1 := by
  simp [pattern]

/--
A prefix table is valid if each entry records the length of the longest proper border of the
corresponding prefix of its pattern.
-/
def IsValid (t : PrefixTable α) : Prop :=
  ∀ i (h : i < t.size),
    List.IsLongestPrefixSuffix t.pattern (t.pattern.take (i + 1)) i t.toArray[i].2

theorem step_of_beq [BEq α] (t : PrefixTable α) (hk : k < t.size)
    (hx : (x == t.toArray[k].1) = true) : (t.step x ⟨k, Nat.lt_succ_of_lt hk⟩).val = k + 1 := by
  rw [step.eq_def]; simp [hk, hx]

theorem step_zero_of_not_beq [BEq α] (t : PrefixTable α)
    (hx : ∀ hk : 0 < t.size, (x == t.toArray[0].1) = false) :
    (t.step x ⟨0, Nat.zero_lt_succ _⟩).val = 0 := by
  rw [step.eq_def]; dsimp only; split <;> simp_all

theorem step_succ_of_not_beq [BEq α] (t : PrefixTable α) (hk : k + 1 < t.size + 1)
    (hx : ∀ hk : k + 1 < t.size, (x == t.toArray[k + 1].1) = false) :
    t.step x ⟨k + 1, hk⟩ = t.step x ⟨(t.toArray[k]'(Nat.lt_of_succ_lt_succ hk)).2,
      Nat.lt_of_le_of_lt (t.valid (Nat.lt_of_succ_lt_succ hk)) (Nat.lt_of_succ_lt hk)⟩ := by
  conv => lhs; rw [step.eq_def]
  dsimp only
  split <;> simp_all

/--
Correctness of the transition function: `t.step x k` is the length of the longest prefix of the
pattern that is a suffix of `t.pattern.take k ++ [x]`.
-/
theorem step_spec [BEq α] [LawfulBEq α] {t : PrefixTable α} (ht : t.IsValid) (x : α)
    (k : Fin (t.size + 1)) :
    List.IsLongestPrefixSuffix t.pattern (t.pattern.take k ++ [x]) t.size (t.step x k).val := by
  obtain ⟨k, hk⟩ := k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  have hp : t.pattern.length = t.size := t.length_pattern
  if hx : ∃ h : k < t.size, t.toArray[k].1 = x then
    obtain ⟨hsz, hx⟩ := hx
    rw [step_of_beq t hsz (beq_iff_eq.2 hx.symm)]
    have := List.isLongestPrefixSuffix_take_succ (p := t.pattern) (by omega : k < _)
    rwa [getElem_pattern, hx, hp] at this
  else
    have hx' : ∀ h : k < t.pattern.length, t.pattern[k] ≠ x := by
      intro h h'; rw [getElem_pattern] at h'; exact hx ⟨by omega, h'⟩
    match k, hk, ih, hx, hx' with
    | 0, _, _, hx, hx' =>
      rw [step_zero_of_not_beq t fun h => beq_eq_false_iff_ne.2 fun h' => hx ⟨h, h'.symm⟩]
      refine ⟨Nat.zero_le _, by simp, fun j hj h => ?_⟩
      exact List.le_of_take_suffix_take_concat (by omega) hx' (by omega) h
    | k + 1, hk, ih, hx, hx' =>
      rw [step_succ_of_not_beq t hk fun h => beq_eq_false_iff_ne.2 fun h' => hx ⟨h, h'.symm⟩]
      have h2 : k < t.size := Nat.lt_of_succ_lt_succ hk
      have hr : List.IsLongestPrefixSuffix t.pattern (t.pattern.take (k + 1)) (k + 1 - 1)
          t.toArray[k].2 := ht k h2
      have hk' : t.toArray[k].2 < k + 1 := Nat.lt_succ_of_le hr.le
      apply (ih _ hk' (Nat.lt_trans hk' hk)).congr
      intro j hj
      refine Iff.symm ?_
      show _ ↔ t.pattern.take j <:+ t.pattern.take t.toArray[k].2 ++ [x]
      have hk1 : k + 1 ≤ t.pattern.length := by omega
      constructor
      · intro h
        have hjk := List.le_of_take_suffix_take_concat hk1 hx' (by omega) h
        exact (List.take_suffix_take_concat_iff_of_border hk1 hr hjk).1 h
      · intro h
        have := List.length_le_of_take_suffix (by omega) h
        simp only [List.length_append, List.length_take, List.length_cons,
          List.length_nil] at this
        exact (List.take_suffix_take_concat_iff_of_border hk1 hr (by omega)).2 h

@[simp] theorem pattern_extend [BEq α] (t : PrefixTable α) (x : α) :
    (t.extend x).pattern = t.pattern ++ [x] := by
  simp [pattern, extend]

@[simp] theorem pattern_default : (default : PrefixTable α).pattern = [] := by
  simp [pattern]; rfl

theorem isValid_default : (default : PrefixTable α).IsValid := nofun

theorem IsValid.extend [BEq α] [LawfulBEq α] {t : PrefixTable α} (ht : t.IsValid) (x : α) :
    (t.extend x).IsValid := by
  intro i hi
  have hp := t.length_pattern
  have htake : ∀ j ≤ t.size, (t.pattern ++ [x]).take j = t.pattern.take j := by
    intro j hj; rw [List.take_append_of_le_length (by omega)]
  have hi2 : i < t.size + 1 := by simpa [PrefixTable.extend, size] using hi
  have hs : t.size = t.toArray.size := rfl
  rw [pattern_extend]
  simp only [PrefixTable.extend]
  rw [Array.getElem_push]
  split
  · next hi' =>
    rw [htake _ (by omega)]
    exact (ht i hi').of_take_eq fun j hj => (htake j (by omega)).symm
  · next hi' =>
    have hi : i = t.size := by omega
    subst hi
    have := step_spec ht x ⟨t.size, Nat.lt_succ_self _⟩
    rw [show t.pattern.take t.size = t.pattern by rw [← hp, List.take_length]] at this
    rw [List.take_of_length_le (by simp)]
    exact this.of_take_eq fun j hj => (htake j hj).symm

theorem IsValid.foldl_extend [BEq α] [LawfulBEq α] {t : PrefixTable α} (ht : t.IsValid)
    (l : List α) : (l.foldl (·.extend) t).IsValid ∧
      (l.foldl (·.extend) t).pattern = t.pattern ++ l := by
  induction l generalizing t with
  | nil => simp [ht]
  | cons x l ih =>
    obtain ⟨h₁, h₂⟩ := ih (ht.extend x)
    exact ⟨h₁, by simp [h₂]⟩

theorem isValid_mkPrefixTable [BEq α] [LawfulBEq α] (xs : Array α) :
    (mkPrefixTable xs).IsValid := by
  rw [mkPrefixTable, ← Array.foldl_toList]
  exact (isValid_default.foldl_extend _).1

@[simp] theorem pattern_mkPrefixTable [BEq α] [LawfulBEq α] (xs : Array α) :
    (mkPrefixTable xs).pattern = xs.toList := by
  rw [mkPrefixTable, ← Array.foldl_toList]
  exact (isValid_default.foldl_extend _).2.trans (by simp)

/--
The KMP automaton tracks the longest prefix of the pattern that is a suffix of the input read so
far.
-/
theorem step_isLongestPrefixSuffix [BEq α] [LawfulBEq α] {t : PrefixTable α} (ht : t.IsValid)
    {k : Fin (t.size + 1)} (h : List.IsLongestPrefixSuffix t.pattern s t.size k) (x : α) :
    List.IsLongestPrefixSuffix t.pattern (s ++ [x]) t.size (t.step x k) := by
  have hp := t.length_pattern
  apply (step_spec ht x k).congr
  intro j hj
  exact (List.take_suffix_concat_iff_of_isLongestPrefixSuffix h (by omega) (by omega)).symm

theorem foldl_step_isLongestPrefixSuffix [BEq α] [LawfulBEq α] {t : PrefixTable α}
    (ht : t.IsValid) {k : Fin (t.size + 1)} (h : List.IsLongestPrefixSuffix t.pattern s t.size k)
    (l : List α) :
    List.IsLongestPrefixSuffix t.pattern (s ++ l) t.size
      (l.foldl (fun k x => t.step x k) k).val := by
  induction l generalizing s k with
  | nil => simpa using h
  | cons x l ih =>
    have := ih (step_isLongestPrefixSuffix ht h x)
    simpa using this

/--
Running the KMP automaton from the initial state over `l` ends in the accepting state exactly when
`l` ends with the pattern.
-/
theorem foldl_step_eq_size_iff [BEq α] [LawfulBEq α] {t : PrefixTable α} (ht : t.IsValid)
    (l : List α) :
    (l.foldl (fun k x => t.step x k) 0).val = t.size ↔ t.pattern <:+ l := by
  have h0 : List.IsLongestPrefixSuffix t.pattern [] t.size (0 : Fin (t.size + 1)) := by
    have := List.isLongestPrefixSuffix_nil t.pattern
    rwa [length_pattern] at this
  have := foldl_step_isLongestPrefixSuffix ht h0 l
  rw [List.nil_append] at this
  exact this.eq_iff_suffix t.length_pattern.symm

end Array.PrefixTable

namespace Array

theorem mkPrefixTable_eq_foldl [BEq α] (xs : Array α) :
    mkPrefixTable xs = xs.toList.foldl (·.extend) default := by
  rw [mkPrefixTable, ← Array.foldl_toList]

theorem mkPrefixTableOfStream_eq [BEq α] [Std.Stream.HasNextRelation σ α] (s : σ)
    [Std.Stream.Finite s] : mkPrefixTableOfStream s = mkPrefixTable (Std.Stream.Finite.toList s).toArray := by
  rw [mkPrefixTableOfStream, Std.Stream.Finite.foldl_eq_foldl_toList, mkPrefixTable_eq_foldl,
    List.toList_toArray]

namespace Matcher
open Std.Stream

/-- Run the KMP automaton of `m` from state `k` over the values `xs`. -/
abbrev run [BEq α] (m : Matcher α) (k : Fin (m.table.size + 1)) (xs : List α) :
    Fin (m.table.size + 1) :=
  xs.foldl (fun k x => m.table.step x k) k

theorem next?_eq_some [BEq α] [HasNextRelation σ α] {m : Matcher α} {s : σ} [Std.Stream.Finite s]
    (h : m.next? s = some (t, m')) :
    ∃ xs, xs ≠ [] ∧ Reads s xs t ∧ m' = { m with state := m.run m.state xs } ∧
      (m.run m.state xs).val = m.table.size ∧
      ∀ i, 0 < i → i < xs.length → (m.run m.state (xs.take i)).val ≠ m.table.size := by
  rw [Matcher.next?.eq_def] at h
  split at h
  · contradiction
  · next x s' hs =>
    have : Std.Stream.Finite s' := .ofSome hs
    dsimp only at h
    split at h
    · next hst =>
      cases h
      exact ⟨[x], by simp, .cons hs (.nil _), rfl, hst, fun i hi hi' => by simp at hi'; omega⟩
    · next hst =>
      obtain ⟨xs, hne, hr, rfl, hsz, hmin⟩ := next?_eq_some h
      refine ⟨x :: xs, by simp, .cons hs hr, rfl, hsz, fun i hi hi' => ?_⟩
      match i with
      | 1 => exact hst
      | j + 2 =>
        have := hmin (j + 1) (by omega) (by simp at hi'; omega)
        simpa [List.take_succ_cons] using this
termination_by Finite.wrap s

theorem next?_eq_none [BEq α] [HasNextRelation σ α] {m : Matcher α} {s : σ} [Std.Stream.Finite s]
    (h : m.next? s = none) :
    ∀ i, 0 < i → i ≤ (Finite.toList s).length →
      (m.run m.state ((Finite.toList s).take i)).val ≠ m.table.size := by
  rw [Matcher.next?.eq_def] at h
  split at h
  · next hs =>
    rw [Finite.toList_none hs]
    intro i hi hi'
    simp at hi'; omega
  · next x s' hs =>
    have : Std.Stream.Finite s' := .ofSome hs
    dsimp only at h
    split at h
    · contradiction
    · next hst =>
      have ih := next?_eq_none h
      rw [Finite.toList_some hs]
      intro i hi hi'
      match i with
      | 1 => simpa using hst
      | j + 2 =>
        have := ih (j + 1) (by omega) (by simp at hi'; omega)
        simpa [List.take_succ_cons] using this
termination_by Finite.wrap s

end Matcher

end Array

theorem Array.Matcher.next?_list_length_lt [BEq α] {m : Matcher α} {l t : List α}
    (h : m.next? l = some (t, m')) : t.length < l.length := by
  obtain ⟨xs, hne, hr, -⟩ := next?_eq_some h
  rw [hr.list, List.length_append]
  cases xs with
  | nil => contradiction
  | cons => simp

theorem Std.Stream.Reads.bsize_lt {s t : Substring.Raw} (h : Reads s xs t) (hne : xs ≠ []) :
    t.bsize < s.bsize := by
  induction h with
  | nil => contradiction
  | @cons s x s' xs t h₁ h₂ ih =>
    have h₁ : s'.bsize < s.bsize := next_of_next?_eq_some h₁
    cases xs with
    | nil => cases h₂; exact h₁
    | cons => exact Nat.lt_trans (ih (by simp)) h₁

theorem Array.Matcher.next?_substring_bsize_lt {m : Matcher Char}
    {s t : Substring.Raw} (h : m.next? s = some (t, m')) : t.bsize < s.bsize := by
  obtain ⟨xs, hne, hr, -⟩ := next?_eq_some h
  exact hr.bsize_lt hne
