/-
Copyright (c) 2023 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/
module

public import BatteriesFiniteStreams.Finite

public section

namespace Array

/-- Prefix table for the Knuth-Morris-Pratt matching algorithm

  This is an array of the form `t = [(x₀,n₀), (x₁,n₁), (x₂, n₂), ...]` where for each `i`, `nᵢ` is
  the length of the longest proper prefix of `xs = [x₀,x₁,...,xᵢ]` which is also a suffix of `xs`.
-/
structure PrefixTable (α : Type _) extends Array (α × Nat) where
  /-- Validity condition to help with termination proofs -/
  valid : (h : i < toArray.size) → toArray[i].2 ≤ i

instance : Inhabited (PrefixTable α) where
  default := ⟨#[], nofun⟩

/-- Returns the size of the prefix table -/
abbrev PrefixTable.size (t : PrefixTable α) := t.toArray.size

/-- Transition function for the KMP matcher

  Assuming we have an input `xs` with a suffix that matches the pattern prefix `t.pattern[:len]`
  where `len : Fin (t.size+1)`. Then `xs.push x` has a suffix that matches the pattern prefix
  `t.pattern[:t.step x len]`. If `len` is as large as possible then `t.step x len` will also be
  as large as possible.
-/
def PrefixTable.step [BEq α] (t : PrefixTable α) (x : α) : Fin (t.size+1) → Fin (t.size+1)
  | ⟨k, hk⟩ =>
    let cont := fun () =>
      match k with
      | 0 => ⟨0, Nat.zero_lt_succ _⟩
      | k + 1 =>
        have h2 : k < t.size := Nat.lt_of_succ_lt_succ hk
        let k' := t.toArray[k].2
        have hk' : k' < k + 1 := Nat.lt_succ_of_le (t.valid h2)
        step t x ⟨k', Nat.lt_trans hk' hk⟩
    if hsz : k < t.size then
      if x == t.toArray[k].1 then
        ⟨k+1, Nat.succ_lt_succ hsz⟩
      else cont ()
    else cont ()
termination_by k => k.val

/-- Extend a prefix table by one element

  If `t` is the prefix table for `xs` then `t.extend x` is the prefix table for `xs.push x`.
-/
def PrefixTable.extend [BEq α] (t : PrefixTable α) (x : α) : PrefixTable α where
  toArray := t.toArray.push (x, t.step x ⟨t.size, Nat.lt_succ_self _⟩)
  valid _ := by
    rw [Array.getElem_push]
    split
    · exact t.valid ..
    · next h => exact Nat.le_trans (Nat.lt_succ_iff.1 <| Fin.isLt ..) (Nat.not_lt.1 h)

/-- Make prefix table from a pattern array -/
def mkPrefixTable [BEq α] (xs : Array α) : PrefixTable α := xs.foldl (·.extend) default

/-- Make prefix table from a finite pattern stream -/
def mkPrefixTableOfStream [BEq α] [Std.Stream.HasNextRelation σ α] (stream : σ)
    [Std.Stream.Finite stream] : PrefixTable α :=
  Std.Stream.Finite.foldl stream (·.extend) default

end Array
