/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.SMOObligations.StrongMultiplicityOneFull

/-!
# Newforms are full Hecke eigenforms (DS Definition 5.8.1, via Strong Multiplicity One)

A `Newform` is by definition (`Newforms/MainLemma.lean`) a `T_n`-eigenform only at the
good primes `(n, N) = 1` (matching Miyake §4.5 / DS §5.5).  This file upgrades that to
**DS Definition 5.8.1**: a `Newform` is a `T_n`-eigenform for **every** `n ∈ ℕ⁺`,
including the bad primes.

## Approach

The classical Atkin–Lehner–Li 1970 derivation establishes the explicit bad-prime
eigenvalues (`±p^{(k-2)/2}` when `p ∥ N`, `0` when `p² ∣ N`) via the `W_p` involution.
We bypass this entirely by invoking the project's **Strong Multiplicity One** result
`HeckeRing.GL2.strongMultiplicityOne_constMul` (`SMOObligations/StrongMultiplicityOneFull.lean`,
Miyake Theorem 4.6.12).

For each `n : ℕ⁺`, the form `T_n f` is itself a `T_q`-eigenform at every `q` coprime to
`N`, sharing all eigenvalues with `f`.  This follows from the unconditional commutativity
`T_n T_q = T_q T_n` (`heckeT_n_comm`) and linearity of `T_n` (`heckeT_n_cusp_smul`):
`T_q (T_n f) = T_n (T_q f) = T_n (a_q • f) = a_q • T_n f`.
Bundled as an `Eigenform`, SMO then forces `T_n f = c • f` for some scalar `c`.

## Main result

* `Newform.toCuspForm_isFullEigenform` : every `Newform N k` is `IsFullEigenform`.

## API additions (general-`n` preservation)

* `heckeT_n_preserves_modFormCharSpace_general` : `T_n` preserves `M_k(Γ₁(N), χ)`
  for **arbitrary** `n` (the existing `heckeT_n_preserves_charSpace` requires
  `(n, N) = 1`).
* `heckeT_n_cusp_preserves_cuspFormCharSpace_general` : cusp-form version.

## References

* **[DS]**  F. Diamond, J. Shurman, *A First Course in Modular Forms*, GTM 228, 2005,
  Definition 5.8.1, Theorem 5.8.2.
* **[Miy]** T. Miyake, *Modular Forms*, 2nd ed., Springer SMM, 2006, §4.5, Theorem 4.6.12.
-/

open CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- A power of the unconditional `heckeT_p_all` preserves `modFormCharSpace k χ`. -/
private lemma heckeT_p_all_pow_preserves_modFormCharSpace
    (k : ℤ) (p : ℕ) (hp : Nat.Prime p) (χ : (ZMod N)ˣ →* ℂˣ) (r : ℕ) :
    ∀ {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}, f ∈ modFormCharSpace k χ →
      (heckeT_p_all k p hp ^ r) f ∈ modFormCharSpace k χ := by
  induction r with
  | zero => intro f hf; simpa using hf
  | succ r ih =>
    intro f hf
    rw [pow_succ, Module.End.mul_apply]
    exact ih (heckeT_p_all_preserves_modFormCharSpace k p hp χ hf)

/-- `heckeT_ppow k p hp r` preserves `modFormCharSpace k χ` for **any** prime `p`
(unconditional on `p`, generalising the coprime version
`Unified.heckeT_ppow_preserves_charSpace'`). -/
private lemma heckeT_ppow_preserves_modFormCharSpace
    (k : ℤ) (p : ℕ) (hp : Nat.Prime p) (χ : (ZMod N)ˣ →* ℂˣ) (r : ℕ)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ modFormCharSpace k χ) :
    heckeT_ppow k p hp r f ∈ modFormCharSpace k χ := by
  by_cases hpN : Nat.Coprime p N
  · exact Unified.heckeT_ppow_preserves_charSpace' p hp hpN r hf
  · rw [heckeT_ppow_eq_pow_of_not_coprime k hp hpN r]
    exact heckeT_p_all_pow_preserves_modFormCharSpace k p hp χ r hf

private lemma heckeT_n_aux_preserves_modFormCharSpace
    (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) (m : ℕ) :
    ∀ {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}, f ∈ modFormCharSpace k χ →
      heckeT_n_aux k m f ∈ modFormCharSpace k χ := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro f hf
    rw [heckeT_n_aux]
    split_ifs with hm
    · simpa using hf
    · push Not at hm
      dsimp only
      set p := m.minFac
      have hp : Nat.Prime p := Nat.minFac_prime (by omega)
      have hm_div_lt : m / p ^ m.factorization p < m :=
        Nat.div_lt_self (by omega) (Nat.one_lt_pow
          (hp.factorization_pos_of_dvd (by omega) (Nat.minFac_dvd m)).ne' hp.one_lt)
      rw [Module.End.mul_apply]
      exact heckeT_ppow_preserves_modFormCharSpace k p hp χ _ (ih _ hm_div_lt hf)

/-- **General-`n` `modFormCharSpace` preservation.**  `heckeT_n k n` preserves
`modFormCharSpace k χ` for **arbitrary** `n` (no coprime-to-`N` hypothesis),
generalising `heckeT_n_preserves_charSpace`. -/
lemma heckeT_n_preserves_modFormCharSpace_general
    (k : ℤ) (n : ℕ) [NeZero n] (χ : (ZMod N)ˣ →* ℂˣ)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ modFormCharSpace k χ) :
    heckeT_n k n f ∈ modFormCharSpace k χ :=
  heckeT_n_aux_preserves_modFormCharSpace k χ n hf

/-- **General-`n` `cuspFormCharSpace` preservation.**  Cusp-form version of
`heckeT_n_preserves_modFormCharSpace_general`. -/
lemma heckeT_n_cusp_preserves_cuspFormCharSpace_general
    (k : ℤ) (n : ℕ) [NeZero n] (χ : (ZMod N)ˣ →* ℂˣ)
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ) :
    heckeT_n_cusp k n f ∈ cuspFormCharSpace k χ :=
  Unified.cuspFormCharSpace_of_toModularForm'_mem <| by
    rw [heckeT_n_cusp_toModularForm']
    exact heckeT_n_preserves_modFormCharSpace_general k n χ
      (Unified.cuspFormCharSpace_toModularForm'_mem hf)

/-- **`T_n f` is a `T_q`-eigenform with the same eigenvalue as `f`, for every
`q` coprime to `N`.**  Uses unconditional commutativity `T_n T_q = T_q T_n`
(`heckeT_n_comm`) and linearity (`heckeT_n_cusp_smul`):
`T_q (T_n f) = T_n (T_q f) = T_n (a_q • f) = a_q • T_n f`. -/
private lemma heckeT_n_cusp_of_newform_isEigen
    (f : Newform N k) (n : ℕ) [NeZero n] (q : ℕ+) (hq : Nat.Coprime q.val N) :
    haveI : NeZero q.val := ⟨q.pos.ne'⟩
    heckeT_n_cusp k q.val (heckeT_n_cusp k n f.toCuspForm) =
      f.eigenvalue q • heckeT_n_cusp k n f.toCuspForm := by
  haveI : NeZero q.val := ⟨q.pos.ne'⟩
  have hcomm : heckeT_n_cusp k q.val (heckeT_n_cusp k n f.toCuspForm) =
      heckeT_n_cusp k n (heckeT_n_cusp k q.val f.toCuspForm) := by
    ext z
    change (heckeT_n k q.val (heckeT_n_cusp k n f.toCuspForm).toModularForm').toFun z =
      (heckeT_n k n (heckeT_n_cusp k q.val f.toCuspForm).toModularForm').toFun z
    rw [heckeT_n_cusp_toModularForm', heckeT_n_cusp_toModularForm']
    simpa [Module.End.mul_apply] using DFunLike.congr_fun (DFunLike.congr_fun
      (heckeT_n_comm (N := N) k q.val n) f.toCuspForm.toModularForm') z
  rw [hcomm, f.isEigen q hq, heckeT_n_cusp_smul]

/-- Bundle `heckeT_n_cusp k n f.toCuspForm` as an `Eigenform N k` with the same
Nebentypus character and ring-eigenvalue family as `f`. -/
private noncomputable def Newform.heckeT_n_cusp_asEigenform
    (f : Newform N k) (n : ℕ) [NeZero n]
    (hfχ : f.toCuspForm ∈ cuspFormCharSpace k f.χ) : Eigenform N k :=
  let Tf : CuspForm ((Gamma1 N).map (mapGL ℝ)) k := heckeT_n_cusp k n f.toCuspForm
  let hTf_charSpace : Tf ∈ cuspFormCharSpace k f.χ :=
    heckeT_n_cusp_preserves_cuspFormCharSpace_general k n f.χ hfχ
  let hTf_isEigen : IsEigenform Tf :=
    ⟨f.eigenvalue, fun q hq ↦ heckeT_n_cusp_of_newform_isEigen f n q hq⟩
  let aux := Unified.isRingEigenvector_of_isEigenform (χ := f.χ) hTf_charSpace hTf_isEigen
  { toCuspForm := Tf
    χ := f.χ
    mem_charSpace := Unified.cuspFormCharSpace_toModularForm'_mem (χ := f.χ) hTf_charSpace
    ringEigenvalue := aux.choose
    isRingEigen := aux.choose_spec }

/-- The classical eigenvalue of `Newform.heckeT_n_cusp_asEigenform` matches
`f.eigenvalue` on the good primes — provided `T_n f ≠ 0`, so that the eigenform
equation can be cancelled. -/
private lemma Newform.heckeT_n_cusp_asEigenform_eigenvalue
    (f : Newform N k) (n : ℕ) [NeZero n]
    (hfχ : f.toCuspForm ∈ cuspFormCharSpace k f.χ)
    (hTn_ne : heckeT_n_cusp k n f.toCuspForm ≠ 0)
    (q : ℕ+) (hq : Nat.Coprime q.val N) :
    (f.heckeT_n_cusp_asEigenform n hfχ).eigenvalue q = f.eigenvalue q := by
  haveI : NeZero q.val := ⟨q.pos.ne'⟩
  set g := f.heckeT_n_cusp_asEigenform n hfχ
  have h_f_isEigen : heckeT_n_cusp k q.val (heckeT_n_cusp k n f.toCuspForm) =
      f.eigenvalue q • heckeT_n_cusp k n f.toCuspForm :=
    heckeT_n_cusp_of_newform_isEigen f n q hq
  rw [show heckeT_n_cusp k q.val (heckeT_n_cusp k n f.toCuspForm) =
    g.eigenvalue q • heckeT_n_cusp k n f.toCuspForm from g.isEigen q hq] at h_f_isEigen
  have h_diff : (g.eigenvalue q - f.eigenvalue q) • heckeT_n_cusp k n f.toCuspForm = 0 := by
    rw [sub_smul, h_f_isEigen, sub_self]
  exact sub_eq_zero.mp <| (smul_eq_zero.mp h_diff).resolve_right hTn_ne

/-- The SMO-supplied scalar `c_n` such that `T_n f = c_n • f` when `T_n f ≠ 0`. -/
private noncomputable def Newform.smoConst
    (f : Newform N k) (n : ℕ) [NeZero n]
    (hfχ : f.toCuspForm ∈ cuspFormCharSpace k f.χ)
    (hTn_ne : heckeT_n_cusp k n f.toCuspForm ≠ 0) : ℂ :=
  (strongMultiplicityOne_constMul f
    (f.heckeT_n_cusp_asEigenform n hfχ) f.χ f.mem_charSpace
    (f.heckeT_n_cusp_asEigenform n hfχ).mem_charSpace ∅
    (fun q hq _ ↦
      (Newform.heckeT_n_cusp_asEigenform_eigenvalue f n hfχ hTn_ne q hq).symm)).choose

private lemma Newform.smoConst_smul_eq
    (f : Newform N k) (n : ℕ) [NeZero n]
    (hfχ : f.toCuspForm ∈ cuspFormCharSpace k f.χ)
    (hTn_ne : heckeT_n_cusp k n f.toCuspForm ≠ 0) :
    heckeT_n_cusp k n f.toCuspForm = f.smoConst n hfχ hTn_ne • f.toCuspForm :=
  (strongMultiplicityOne_constMul f
    (f.heckeT_n_cusp_asEigenform n hfχ) f.χ f.mem_charSpace
    (f.heckeT_n_cusp_asEigenform n hfχ).mem_charSpace ∅
    (fun q hq _ ↦
      (Newform.heckeT_n_cusp_asEigenform_eigenvalue f n hfχ hTn_ne q hq).symm)).choose_spec

/-- **DS Definition 5.8.1: a `Newform` is a `T_n`-eigenform for every `n ∈ ℕ⁺`.**

We bypass the classical Atkin–Lehner–Li derivation of explicit bad-prime eigenvalues
(`±p^{(k-2)/2}` when `p ∥ N`, `0` when `p² ∣ N`) by invoking Strong Multiplicity One
(`strongMultiplicityOne_constMul`, Miyake Theorem 4.6.12): for each `n`, the form
`T_n f` is a `T_q`-eigenform at every `q` coprime to `N` sharing all of `f`'s
eigenvalues, so SMO forces `T_n f = c • f` for some scalar `c`. -/
theorem Newform.toCuspForm_isFullEigenform (f : Newform N k) :
    IsFullEigenform f.toCuspForm := by
  classical
  have hfχ : f.toCuspForm ∈ cuspFormCharSpace k f.χ :=
    Unified.cuspFormCharSpace_of_toModularForm'_mem f.mem_charSpace
  refine ⟨fun n ↦
    haveI : NeZero n.val := ⟨n.pos.ne'⟩
    if hTn_ne : heckeT_n_cusp k n.val f.toCuspForm = 0 then (0 : ℂ)
    else f.smoConst n.val hfχ hTn_ne, fun n ↦ ?_⟩
  haveI : NeZero n.val := ⟨n.pos.ne'⟩
  by_cases hTn_ne : heckeT_n_cusp k n.val f.toCuspForm = 0
  · simp [hTn_ne]
  · simpa [dif_neg hTn_ne] using f.smoConst_smul_eq n.val hfχ hTn_ne

end HeckeRing.GL2
