/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import LeanModularForms.Modularforms.Icc_Ico_lems

@[expose] public section

/-!
# `limUnder` lemmas for complex Cauchy sequences

We collect algebraic and convergence lemmas for `limUnder atTop` applied to complex Cauchy
sequences, plus a `tsum`-as-`limUnder` identity for integer-indexed sums.
-/

open TopologicalSpace Set Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

/-- The limit of a sum of Cauchy sequences equals the sum of their limits. -/
lemma limUnder_add {α : Type*} [Preorder α] [(atTop : Filter α).NeBot] (f g : α → ℂ)
    (hf : CauchySeq f) (hg : CauchySeq g) :
    limUnder atTop f + limUnder atTop g = limUnder atTop (f + g) := by
  nth_rw 3 [Filter.Tendsto.limUnder_eq]
  rw [Pi.add_def]
  exact (hf.tendsto_limUnder).add hg.tendsto_limUnder

/-- The limit of a scalar multiple of a Cauchy sequence equals the scalar multiple of its
limit. -/
lemma limUnder_mul_const {α : Type*} [Preorder α] [(atTop : Filter α).NeBot] (f : α → ℂ)
    (hf : CauchySeq f) (c : ℂ) :
    c * limUnder atTop f = limUnder atTop (c • f) := by
  nth_rw 2 [Filter.Tendsto.limUnder_eq]
  exact hf.tendsto_limUnder.const_mul c

/-- The limit of a difference of Cauchy sequences equals the difference of their limits. -/
lemma limUnder_sub {α : Type*} [Preorder α] [(atTop : Filter α).NeBot] (f g : α → ℂ)
    (hf : CauchySeq f) (hg : CauchySeq g) :
    limUnder atTop f - limUnder atTop g = limUnder atTop (f - g) := by
  nth_rw 3 [Filter.Tendsto.limUnder_eq]
  rw [Pi.sub_def]
  exact hf.tendsto_limUnder.sub hg.tendsto_limUnder

/-- Two Cauchy sequences that agree eventually have the same limit. -/
lemma limUnder_congr_eventually (f g : ℕ → ℂ) (h : ∀ᶠ n in atTop, f n = g n)
    (hf : CauchySeq f) (hg : CauchySeq g) :
    limUnder atTop f = limUnder atTop g := by
  rw [Filter.Tendsto.limUnder_eq (x := limUnder atTop f) hf.tendsto_limUnder,
    Filter.Tendsto.limUnder_eq (hg.tendsto_limUnder.congr' (h.mono fun _ ↦ Eq.symm))]

/-- A summable function over `ℤ` can be summed as the limit of symmetric partial sums. -/
lemma tsum_limUnder_atTop (f : ℤ → ℂ) (hf : Summable f) :
    ∑' n, f n = limUnder atTop (fun N : ℕ ↦ ∑ n ∈ Finset.Ico (-N : ℤ) N, f n) := by
  rw [Filter.Tendsto.limUnder_eq]
  exact hf.hasSum.comp verga
