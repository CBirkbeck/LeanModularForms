/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.HeckeRIngs.GL2.AdjointTheoryPetersson
import LeanModularForms.HeckeRIngs.GL2.CharacterDecomp
import LeanModularForms.HeckeRIngs.GL2.LevelEmbed
import LeanModularForms.HeckeRIngs.GL2.LevelRaise
import LeanModularForms.HeckeRIngs.GL2.Unified.NebentypusHeckeRingHom
import LeanModularForms.Modularforms.LFunction
import LeanModularForms.Modularforms.PeterssonLevelN
import LeanModularForms.Modularforms.DimensionFormulas
import LeanModularForms.Modularforms.SlashActionAuxil
import LeanModularForms.Eigenforms.ConductorTheorem
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import LeanModularForms.HeckeRIngs.GL2.Newforms.MellinBridges

/-!
# Newforms: bad-prime Fricke adjoint candidate and the extended newspace

The bad-prime Hecke linear map and Fricke adjoint candidate (T148) with its auxiliary discharges, the scalar-corrected bad-prime Fricke `petN` adjoint (T149), and the T174-T180 extended-oldspace / extended-newspace API (`NewformExtended`) for the SMO route.

This module is part of the split of `Newforms.lean`; see that file's header
for the overall design.  Declarations are kept in their original order.
-/

noncomputable section

namespace HeckeRing.GL2

open CongruenceSubgroup Matrix.SpecialLinearGroup CuspForm
open HeckeRing.GL2.Unified
open scoped MatrixGroups ModularForm Pointwise DirectSum

variable {N : ℕ} [NeZero N] {k : ℤ}
/-! ### Bad-prime Hecke linear-map and Fricke adjoint candidate (T148) -/

/-- **`heckeT_n_cusp k n` packaged as a `ℂ`-linear endomorphism of cusp forms (T148).**

The bad-prime Hecke operator `heckeT_n_cusp k n` is linear (proven separately as
`heckeT_n_cusp_add` / `heckeT_n_cusp_smul`); this lemma packages it as a
`LinearMap` so it can be composed with `Newform.frickeSlashCuspForm` to form
the Fricke-conjugated adjoint candidate. -/
noncomputable def Newform.heckeT_n_cusp_lin
    {N : ℕ} [NeZero N] (k : ℤ) (n : ℕ) [NeZero n] :
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ]
      CuspForm ((Gamma1 N).map (mapGL ℝ)) k where
  toFun := heckeT_n_cusp k n
  map_add' := heckeT_n_cusp_add n
  map_smul' c f := heckeT_n_cusp_smul n c f

@[simp]
lemma Newform.heckeT_n_cusp_lin_apply
    {N : ℕ} [NeZero N] (k : ℤ) (n : ℕ) [NeZero n]
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    Newform.heckeT_n_cusp_lin k n f = heckeT_n_cusp k n f :=
  rfl

/-- **Bad-prime Fricke-conjugated adjoint candidate (T148).**

Definition `T_adj := frickeSlashCuspForm ∘ heckeT_n_cusp_lin k p ∘ frickeSlashCuspForm`,
the `W_N · T_p · W_N`-style conjugate operator (with the involution-up-to-scalar
T144 `frickeSquareScalar = (-1)^k · N^{k-2}` absorbed at the petN level).

For the bad-prime case `p ∣ N`, the classical Atkin-Lehner adjoint formula
asserts that `pet (T_p f) g = (some scalar) · pet f (T_adj g)` and that
`T_adj` preserves the old subspace; both are needed to apply the T140
conditional newspace-preservation reducer.

This definition packages the operator. The petN adjoint identity and oldspace
preservation are stated separately as named hypotheses for downstream
discharge. -/
noncomputable def Newform.frickeBadAdjointCandidate
    {N : ℕ} [NeZero N] (k : ℤ) (p : ℕ) [NeZero p] :
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ]
      CuspForm ((Gamma1 N).map (mapGL ℝ)) k :=
  Newform.frickeSlashCuspForm ∘ₗ Newform.heckeT_n_cusp_lin k p ∘ₗ
    Newform.frickeSlashCuspForm

@[simp]
lemma Newform.frickeBadAdjointCandidate_apply
    {N : ℕ} [NeZero N] (k : ℤ) (p : ℕ) [NeZero p]
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    Newform.frickeBadAdjointCandidate k p g =
      Newform.frickeSlashCuspForm
        (heckeT_n_cusp k p (Newform.frickeSlashCuspForm g)) := by
  rfl

/-- **Bad-prime newspace preservation, conditional on the petN-adjoint identity
and the Fricke-bad-adjoint oldspace preservation (T148 main partial).**

For p prime with p ∣ N (i.e., `¬ Nat.Coprime p N`), the bad-prime Hecke operator
`heckeT_n_cusp k p` preserves `cuspFormsNew N k` provided two named hypotheses:

* `h_adj`: the petN adjoint relation
  `petN (heckeT_n_cusp k p f) g = petN f (frickeBadAdjointCandidate k p g)`.

* `h_old`: `frickeBadAdjointCandidate k p` preserves `cuspFormsOld N k`.

Both hypotheses follow from the classical Atkin-Lehner adjoint theory. The
proof is a direct application of T140's
`heckeT_n_cusp_preserves_cuspFormsNew_at_divN_of_petersson_adjoint` with
`T_adj := frickeBadAdjointCandidate k p`. -/
theorem Newform.heckeT_n_cusp_preserves_cuspFormsNew_at_divN_of_fricke_adjoint
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p] (hp : p.Prime)
    (hpN : ¬ Nat.Coprime p N)
    (h_adj : ∀ (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
      petN (heckeT_n_cusp k p f) g =
        petN f (Newform.frickeBadAdjointCandidate k p g))
    (h_old : ∀ (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
      g ∈ cuspFormsOld N k →
        Newform.frickeBadAdjointCandidate k p g ∈ cuspFormsOld N k)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (hf : f ∈ cuspFormsNew N k) :
    heckeT_n_cusp k p f ∈ cuspFormsNew N k :=
  heckeT_n_cusp_preserves_cuspFormsNew_at_divN_of_petersson_adjoint hp hpN
    (Newform.frickeBadAdjointCandidate k p) h_adj h_old f hf

/-! ### Auxiliary discharges for `frickeBadAdjointCandidate` (T148) -/

/-- **`Newform.frickeSlashCuspForm` preserves `cuspFormsOld N k` (T148 helper).**

The Atkin-Lehner involution `f ↦ f ∣[k] W_N` maps oldforms to oldforms. This
is reduced to the structural claim that for any `levelRaise`-image
`heq ▸ levelRaise M d k h` (where `d * M = N, d > 1`), its Fricke slash is
again a level-raised form, i.e., it lies in the span of oldform generators.

This claim is **not yet proved** in the present pass. Stated as a named
hypothesis for downstream discharge. The classical proof: lifting via the
explicit `levelRaise` matrix and using `frickeMatrix_mul_self_val` (T141) to
conjugate level-raise matrices, reducing to a level-raise identity at level
`d`. The full proof requires a non-trivial level-raise / Atkin-Lehner
commutativity statement that is a substantial theorem in its own right. -/
def Newform.HasFrickeSlashCuspFormPreservesCuspFormsOld
    (N : ℕ) [NeZero N] (k : ℤ) : Prop :=
  ∀ (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
    g ∈ cuspFormsOld N k → Newform.frickeSlashCuspForm g ∈ cuspFormsOld N k

/-- **Matrix-level Fricke / level-raise commutation identity (T172 support).**

The Atkin-Lehner / Fricke matrix `W_M = !![0, -1; M, 0]` post-multiplied by the
level-raising matrix `α_d = !![d, 0; 0, 1]` equals `W_N` where `N = d * M`:

```
W_M · α_d = !![0, -1; M, 0] · !![d, 0; 0, 1]
          = !![0·d + (-1)·0, 0·0 + (-1)·1; M·d + 0·0, M·0 + 0·1]
          = !![0, -1; M·d, 0]
          = !![0, -1; N, 0]
          = W_N.
```

This is the **clean matrix identity** linking `W_N` and `W_M` via the level-raise
matrix `α_d`, the foundation for the function-level `g ∣[k] W_N = (g ∣[k] W_M) ∣[k] α_d`
slash identity used in the Atkin-Lehner / oldspace preservation chain.

Proof: `Units.ext` reduces to entry-wise equality of `2 × 2` matrices, then
`fin_cases` + `simp` with the explicit matrix entries closes each case. -/
lemma Newform.frickeMatrix_mul_levelRaiseMatrix
    {M : ℕ} [NeZero M] {d : ℕ} [NeZero d] :
    haveI : NeZero (d * M) := ⟨Nat.mul_ne_zero (NeZero.ne d) (NeZero.ne M)⟩
    (Newform.frickeMatrix M : GL (Fin 2) ℝ) *
        HeckeRing.GL2.levelRaiseMatrix d =
      Newform.frickeMatrix (d * M) := by
  haveI : NeZero (d * M) := ⟨Nat.mul_ne_zero (NeZero.ne d) (NeZero.ne M)⟩
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Newform.frickeMatrix, HeckeRing.GL2.levelRaiseMatrix,
      Matrix.GeneralLinearGroup.mkOfDetNeZero, Units.val_mul, Matrix.mul_apply,
      Fin.sum_univ_two, mul_comm d M]

/-- **T172 reduction: `HasFrickeSlashCuspFormPreservesCuspFormsOld` reduces
to its level-raise generators.**

Direct consumer reducing `Newform.HasFrickeSlashCuspFormPreservesCuspFormsOld`
to the **single explicit residual statement**: that for every level-raise
oldform generator `f = heq ▸ levelRaise M d k g` (with `1 < d` and `d * M = N`),
the Fricke slash `Newform.frickeSlashCuspForm f` lies in `cuspFormsOld N k`.

This is a clean equivalence: the forward direction follows by applying the
preservation Prop to any generator (a generator lies in the span hence in
`cuspFormsOld`); the backward direction extends the per-generator statement
to all of `cuspFormsOld N k` via `Submodule.span_induction`, using linearity
of `Newform.frickeSlashCuspForm` (a `LinearMap`) and the standard
zero/add/smul closure of `cuspFormsOld N k` (a `Submodule`).

This packages the Prop's content cleanly so any future worker only needs to
prove the per-generator statement, without re-doing the span-induction
plumbing every time. -/
theorem Newform.hasFrickeSlashCuspFormPreservesCuspFormsOld_iff_on_generators
    {N : ℕ} [NeZero N] {k : ℤ} :
    Newform.HasFrickeSlashCuspFormPreservesCuspFormsOld N k ↔
      ∀ (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
        IsOldformGenerator f →
          Newform.frickeSlashCuspForm f ∈ cuspFormsOld N k := by
  constructor
  · intro h_pres f h_gen
    exact h_pres f (Submodule.subset_span h_gen)
  · intro h_gen f hf
    refine Submodule.span_induction
      (p := fun (x : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) _ =>
        Newform.frickeSlashCuspForm x ∈ cuspFormsOld N k)
      ?_ ?_ ?_ ?_ hf
    · intro f₀ h_f₀_gen
      exact h_gen f₀ h_f₀_gen
    · show Newform.frickeSlashCuspForm
        (0 : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∈ cuspFormsOld N k
      rw [map_zero]
      exact Submodule.zero_mem _
    · intro x y _ _ ihx ihy
      show Newform.frickeSlashCuspForm (x + y) ∈ cuspFormsOld N k
      rw [map_add]
      exact Submodule.add_mem _ ihx ihy
    · intro c x _ ihx
      show Newform.frickeSlashCuspForm (c • x) ∈ cuspFormsOld N k
      rw [map_smul]
      exact Submodule.smul_mem _ c ihx

/-- **T172 — Conditional preservation theorem for `cuspFormsOldExtended`
(Round 2 deliverable).**

`Newform.frickeSlashCuspForm` preserves `cuspFormsOldExtended N k`, conditional
on the **per-generator preservation hypothesis**: that for every member of the
disjoint generator family `IsOldformGenerator f ∨ IsLevelInclusionOldformGenerator f`
of `cuspFormsOldExtended`, the Fricke slash `frickeSlashCuspForm f` lies in
`cuspFormsOldExtended N k`.

This is the **direct consumer** packaging the span-induction plumbing for
Primary's extended oldspace API: any future worker discharging the
per-generator obligation on the disjunction (which decomposes into:

* **level-raise generator case** `f = heq ▸ levelRaise M d k g₀`:
  by `Newform.frickeMatrix_mul_levelRaiseMatrix` (the matrix identity
  `W_M · α_d = W_(d*M)`) plus slash-formula computation, the Fricke slash
  rewrites to a scalar multiple of the **trivial inclusion** of the level-`M`
  Fricke `frickeSlashCuspForm-at-M g₀`, and that lies in
  `cuspFormsOldExtended` via `levelInclude_cusp_mem_cuspFormsOldExtended`;

* **trivial-inclusion generator case** `f = levelInclude_cusp hMN k g₀`:
  by the same matrix identity plus slash composition, the Fricke slash rewrites
  to a scalar multiple of a **level-raise** of the level-`M` Fricke, which is
  an `IsOldformGenerator` and hence in `cuspFormsOld N k ⊆ cuspFormsOldExtended`)

immediately closes the full preservation theorem via this consumer.

Forward direction is trivial (`Submodule.subset_span` from generator → span).
Backward direction is the standard `Submodule.span_induction` with the
disjunction generator case + zero/add/smul closure via `LinearMap` linearity
of `Newform.frickeSlashCuspForm` and `Submodule` closure properties. -/
theorem Newform.frickeSlashCuspForm_preserves_cuspFormsOldExtended_iff_on_generators
    {N : ℕ} [NeZero N] {k : ℤ} :
    (∀ (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
        g ∈ cuspFormsOldExtended N k →
        Newform.frickeSlashCuspForm g ∈ cuspFormsOldExtended N k) ↔
      ∀ (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
        (IsOldformGenerator f ∨ IsLevelInclusionOldformGenerator f) →
          Newform.frickeSlashCuspForm f ∈ cuspFormsOldExtended N k := by
  constructor
  · intro h_pres f h_gen
    exact h_pres f (Submodule.subset_span h_gen)
  · intro h_gen g hg
    refine Submodule.span_induction
      (p := fun (x : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) _ =>
        Newform.frickeSlashCuspForm x ∈ cuspFormsOldExtended N k)
      ?_ ?_ ?_ ?_ hg
    · intro f₀ h_f₀_gen
      exact h_gen f₀ h_f₀_gen
    · show Newform.frickeSlashCuspForm
          (0 : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∈ cuspFormsOldExtended N k
      rw [map_zero]
      exact Submodule.zero_mem _
    · intro x y _ _ ihx ihy
      show Newform.frickeSlashCuspForm (x + y) ∈ cuspFormsOldExtended N k
      rw [map_add]
      exact Submodule.add_mem _ ihx ihy
    · intro c x _ ihx
      show Newform.frickeSlashCuspForm (c • x) ∈ cuspFormsOldExtended N k
      rw [map_smul]
      exact Submodule.smul_mem _ c ihx

/-- **T173 — Fricke slash of a trivial-inclusion oldform generator lands in
`cuspFormsOldExtended` (Case B per-generator residual).**

For any proper divisor `M < N` (with `M ∣ N`), the Atkin-Lehner / Fricke
involution applied to a trivially-included level-`M` cusp form lands in the
extended oldspace `cuspFormsOldExtended N k` at level `N`.

**Mathematical content.** With `d := N / M > 1`, the matrix identity
`Newform.frickeMatrix_mul_levelRaiseMatrix` gives `W_N = W_M · α_d`, so
slashing `g` at level `M` by `W_N` factors as `g ∣[k] W_N = (g ∣[k] W_M) ∣[k] α_d`.
The outer slash by `α_d` is exactly `d^{k-1} · levelRaiseFun d k ·`, so the
overall identity is

```
frickeSlashCuspForm (levelInclude_cusp hMN k g)
  = (d : ℂ)^(k - 1) • (heq ▸ levelRaise M d k (frickeSlashCuspForm-at-M g))
```

where the right-hand side is a scalar multiple of an `IsOldformGenerator`
(level-raise from `M` with `d > 1`), hence in `cuspFormsOld N k ⊆
cuspFormsOldExtended N k`. -/
theorem Newform.frickeSlashCuspForm_levelInclude_cusp_mem_cuspFormsOldExtended
    {N : ℕ} [NeZero N] {M : ℕ} [NeZero M] (hMN : M ∣ N) (hMltN : M < N) {k : ℤ}
    (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    Newform.frickeSlashCuspForm (levelInclude_cusp hMN k g) ∈
      cuspFormsOldExtended N k := by
  -- Clone hMN, then destructure the clone to get a free `d` (not let-bound).
  have hMN_copy : M ∣ N := hMN
  obtain ⟨d, hd⟩ := hMN_copy
  have hd_pos : 0 < d := by
    rcases Nat.eq_zero_or_pos d with hd_zero | hd_pos
    · exfalso; rw [hd_zero, Nat.mul_zero] at hd
      exact NeZero.ne N hd
    · exact hd_pos
  haveI : NeZero d := ⟨Nat.pos_iff_ne_zero.mp hd_pos⟩
  have hd_lt : 1 < d := by
    by_contra h_le
    push_neg at h_le
    have hd_eq : d = 1 := le_antisymm h_le hd_pos
    rw [hd_eq, Nat.mul_one] at hd
    exact hMltN.ne hd.symm
  haveI : NeZero (d * M) := ⟨Nat.mul_ne_zero (NeZero.ne d) (NeZero.ne M)⟩
  -- Replace N with d * M via subst (d is a free var now, so this should work).
  have heq_N : N = d * M := by rw [mul_comm]; exact hd
  subst heq_N
  -- After subst, the goal references d * M instead of N.
  let Y : CuspForm ((Gamma1 M).map (mapGL ℝ)) k :=
    @Newform.frickeSlashCuspForm M _ k g
  let f_witness : CuspForm ((Gamma1 (d * M)).map (mapGL ℝ)) k :=
    levelRaise M d k Y
  have h_gen : IsOldformGenerator f_witness :=
    ⟨M, d, inferInstance, inferInstance, hd_lt, rfl, Y, rfl⟩
  suffices h_eq : Newform.frickeSlashCuspForm (levelInclude_cusp hMN k g) =
      (d : ℂ) ^ (k - 1) • f_witness by
    rw [h_eq]
    exact Submodule.smul_mem _ _
      (cuspFormsOld_le_cuspFormsOldExtended (Submodule.subset_span h_gen))
  apply CuspForm.ext
  intro τ
  -- Matrix identity W_(d*M) = W_M * α_d.
  have h_matrix : (Newform.frickeMatrix (d * M) : GL (Fin 2) ℝ) =
      (Newform.frickeMatrix M : GL (Fin 2) ℝ) *
        (HeckeRing.GL2.levelRaiseMatrix d : GL (Fin 2) ℝ) :=
    (Newform.frickeMatrix_mul_levelRaiseMatrix (M := M) (d := d)).symm
  have hd_ne : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have h_zpow_cancel : ((d : ℂ) ^ (k - 1)) * ((d : ℂ) ^ (1 - k)) = 1 := by
    rw [← zpow_add₀ hd_ne]
    rw [show (k - 1) + (1 - k) = (0 : ℤ) from by ring]
    exact zpow_zero _
  show (⇑(Newform.frickeSlashCuspForm
      (levelInclude_cusp hMN k g)) : UpperHalfPlane → ℂ) τ =
      (⇑((d : ℂ) ^ (k - 1) • f_witness) : UpperHalfPlane → ℂ) τ
  rw [show (⇑(Newform.frickeSlashCuspForm
        (levelInclude_cusp hMN k g)) : UpperHalfPlane → ℂ) =
      (⇑(levelInclude_cusp hMN k g) : UpperHalfPlane → ℂ) ∣[k]
        (Newform.frickeMatrix (d * M) : GL (Fin 2) ℝ) from rfl]
  rw [show (⇑(levelInclude_cusp hMN k g) : UpperHalfPlane → ℂ) = ⇑g from rfl]
  rw [h_matrix, SlashAction.slash_mul]
  show ((⇑g ∣[k] (Newform.frickeMatrix M : GL (Fin 2) ℝ)) ∣[k]
        (HeckeRing.GL2.levelRaiseMatrix d : GL (Fin 2) ℝ)) τ =
    ((d : ℂ) ^ (k - 1)) * ((⇑f_witness : UpperHalfPlane → ℂ) τ)
  -- f_witness = levelRaise M d k Y at level d*M (no heq cast, by def).
  show ((⇑g ∣[k] (Newform.frickeMatrix M : GL (Fin 2) ℝ)) ∣[k]
        (HeckeRing.GL2.levelRaiseMatrix d : GL (Fin 2) ℝ)) τ =
    ((d : ℂ) ^ (k - 1)) * ((⇑(levelRaise M d k Y) : UpperHalfPlane → ℂ) τ)
  rw [show (⇑(levelRaise M d k Y) : UpperHalfPlane → ℂ) τ =
      ((d : ℂ) ^ (1 - k)) *
        ((⇑Y : UpperHalfPlane → ℂ) ∣[k]
          (HeckeRing.GL2.levelRaiseMatrix d : GL (Fin 2) ℝ)) τ from rfl]
  rw [show (⇑Y : UpperHalfPlane → ℂ) = ⇑g ∣[k]
      (Newform.frickeMatrix M : GL (Fin 2) ℝ) from rfl]
  rw [show ((d : ℂ) ^ (k - 1)) *
        (((d : ℂ) ^ (1 - k)) *
          (((⇑g ∣[k] (Newform.frickeMatrix M : GL (Fin 2) ℝ)) ∣[k]
            (HeckeRing.GL2.levelRaiseMatrix d : GL (Fin 2) ℝ)) τ)) =
      (((d : ℂ) ^ (k - 1)) * ((d : ℂ) ^ (1 - k))) *
        (((⇑g ∣[k] (Newform.frickeMatrix M : GL (Fin 2) ℝ)) ∣[k]
          (HeckeRing.GL2.levelRaiseMatrix d : GL (Fin 2) ℝ)) τ) from by ring]
  rw [h_zpow_cancel, one_mul]

/-- **T173 — UpperHalfPlane action identity `α_d • (W_(d*M) • τ) = W_M • τ`.**

The matrix identity `W_M · α_d = W_(d*M)` (via `Newform.frickeMatrix_mul_levelRaiseMatrix`)
combined with the GL₂-action on `ℍ` gives the pointwise equality
`α_d • (W_(d*M) • τ) = W_M • τ`. Both sides equal `-1/(M · τ)` as complex numbers
(since `(W_(d*M) • τ).val = -1/(d*M·τ)` and `α_d` scales by `d`, so
`d · (-1/(d*M·τ)) = -1/(M·τ)` matches `(W_M • τ).val`).

This is the key equality used in the level-raise generator case of T173. -/
private lemma alpha_d_smul_frickeMatrix_dM_smul_eq_frickeMatrix_M_smul
    {M : ℕ} [NeZero M] {d : ℕ} [NeZero d] (τ : UpperHalfPlane) :
    haveI : NeZero (d * M) := ⟨Nat.mul_ne_zero (NeZero.ne d) (NeZero.ne M)⟩
    (HeckeRing.GL2.levelRaiseMatrix d : GL (Fin 2) ℝ) •
        ((Newform.frickeMatrix (d * M) : GL (Fin 2) ℝ) • τ) =
      (Newform.frickeMatrix M : GL (Fin 2) ℝ) • τ := by
  haveI : NeZero (d * M) := ⟨Nat.mul_ne_zero (NeZero.ne d) (NeZero.ne M)⟩
  apply UpperHalfPlane.ext
  rw [coe_levelRaiseMatrix_smul, Newform.frickeMatrix_smul, Newform.frickeMatrix_smul]
  have hd_ne : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have hM_ne : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
  have hτ_ne : (τ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ
  push_cast
  field_simp

/-- **T173 — Fricke slash of a level-raise oldform generator lands in
`cuspFormsOldExtended` (Case A per-generator residual).**

For any proper divisor `M` of `N` with `d := N/M > 1`, the Atkin-Lehner / Fricke
involution applied to a level-raised cusp form `levelRaise M d k g₀` lands in the
extended oldspace `cuspFormsOldExtended N k`.

**Mathematical content.** With `N = d * M`, the matrix identity
`W_M · α_d = W_N` (`Newform.frickeMatrix_mul_levelRaiseMatrix`) plus the
UpperHalfPlane action equality `α_d • (W_N • τ) = W_M • τ`
(`alpha_d_smul_frickeMatrix_dM_smul_eq_frickeMatrix_M_smul`) yields the
function-level identity

```
frickeSlashCuspForm (heq ▸ levelRaise M d k g₀)
  = (d : ℂ)⁻¹ • levelInclude_cusp hMN k (frickeSlashCuspForm-at-M g₀)
```

The right-hand side is a scalar multiple of the trivial inclusion of the level-`M`
Fricke, hence in `cuspFormsOldExtended N k` via
`levelInclude_cusp_mem_cuspFormsOldExtended`. -/
theorem Newform.frickeSlashCuspForm_levelRaise_mem_cuspFormsOldExtended
    {N : ℕ} [NeZero N] {M : ℕ} [NeZero M]
    {d : ℕ} [NeZero d] (hd_lt : 1 < d) (heq : d * M = N) {k : ℤ}
    (g₀ : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    Newform.frickeSlashCuspForm (heq ▸ levelRaise M d k g₀) ∈
      cuspFormsOldExtended N k := by
  -- Replace N with d * M everywhere via subst.
  subst heq
  -- After subst, [NeZero (d * M)] is in scope from the original [NeZero N].
  -- Goal is now: frickeSlashCuspForm (levelRaise M d k g₀) ∈ cuspFormsOldExtended (d * M) k.
  -- M ∣ d * M and M < d * M.
  have hMN : M ∣ d * M := ⟨d, (mul_comm d M)⟩
  have hMltN : M < d * M := by
    have hM_pos : 0 < M := Nat.pos_of_neZero M
    nlinarith [hd_lt, hM_pos]
  set h_inclusion : CuspForm ((Gamma1 (d * M)).map (mapGL ℝ)) k :=
    levelInclude_cusp hMN k (Newform.frickeSlashCuspForm g₀) with h_inc_def
  have h_inc_mem : h_inclusion ∈ cuspFormsOldExtended (d * M) k :=
    levelInclude_cusp_mem_cuspFormsOldExtended hMN hMltN _
  suffices h_eq : Newform.frickeSlashCuspForm (levelRaise M d k g₀) =
      (d : ℂ)⁻¹ • h_inclusion by
    rw [h_eq]
    exact Submodule.smul_mem _ _ h_inc_mem
  apply CuspForm.ext
  intro τ
  have hd_ne : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have hM_ne : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
  have hτ_ne : (τ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ
  -- LHS: ⇑(frickeSlashCuspForm (levelRaise M d k g₀)) τ
  --    = (⇑(levelRaise M d k g₀) ∣[k] W_(d*M)) τ
  show (⇑(Newform.frickeSlashCuspForm
        (levelRaise M d k g₀)) : UpperHalfPlane → ℂ) τ =
      (⇑((d : ℂ)⁻¹ • h_inclusion) : UpperHalfPlane → ℂ) τ
  rw [show (⇑(Newform.frickeSlashCuspForm
          (levelRaise M d k g₀)) : UpperHalfPlane → ℂ) =
      (⇑(levelRaise M d k g₀) : UpperHalfPlane → ℂ) ∣[k]
        (Newform.frickeMatrix (d * M) : GL (Fin 2) ℝ) from rfl]
  rw [Newform.frickeMatrix_slash_apply]
  rw [show (⇑(levelRaise M d k g₀) : UpperHalfPlane → ℂ)
        ((Newform.frickeMatrix (d * M) : GL (Fin 2) ℝ) • τ) =
      levelRaiseFun d k (⇑g₀)
        ((Newform.frickeMatrix (d * M) : GL (Fin 2) ℝ) • τ) from rfl]
  rw [levelRaiseFun_apply]
  -- UpperHalfPlane action equality: α_d • (W_(d*M) • τ) = W_M • τ.
  rw [alpha_d_smul_frickeMatrix_dM_smul_eq_frickeMatrix_M_smul]
  show ⇑g₀ ((Newform.frickeMatrix M : GL (Fin 2) ℝ) • τ) *
        ((↑(d * M) : ℝ) : ℂ) ^ (k - 1) * (((d * M : ℕ) : ℂ) * (τ : ℂ)) ^ (-k) =
      (⇑((d : ℂ)⁻¹ • h_inclusion) : UpperHalfPlane → ℂ) τ
  rw [show (⇑((d : ℂ)⁻¹ • h_inclusion) : UpperHalfPlane → ℂ) τ =
        (d : ℂ)⁻¹ * (⇑h_inclusion : UpperHalfPlane → ℂ) τ from rfl]
  rw [show (⇑h_inclusion : UpperHalfPlane → ℂ) =
        (⇑(Newform.frickeSlashCuspForm g₀) : UpperHalfPlane → ℂ) from rfl]
  rw [show (⇑(Newform.frickeSlashCuspForm g₀) : UpperHalfPlane → ℂ) =
        (⇑g₀ : UpperHalfPlane → ℂ) ∣[k]
          (Newform.frickeMatrix M : GL (Fin 2) ℝ) from rfl]
  rw [Newform.frickeMatrix_slash_apply]
  -- Convert (d * M : ℕ) casts to (d : ℂ) * (M : ℂ).
  rw [show (((d * M : ℕ) : ℝ) : ℂ) = (d : ℂ) * (M : ℂ) from by push_cast; ring]
  rw [show (((d * M : ℕ) : ℂ) * (τ : ℂ)) =
        (d : ℂ) * (M : ℂ) * (τ : ℂ) from by push_cast; ring]
  rw [mul_zpow]
  rw [show ((d : ℂ) * (M : ℂ) * (τ : ℂ)) ^ (-k) =
        ((d : ℂ) * (M : ℂ)) ^ (-k) * (τ : ℂ) ^ (-k) from
      mul_zpow ((d : ℂ) * (M : ℂ)) (τ : ℂ) (-k)]
  rw [show (((d : ℂ) * (M : ℂ)) ^ (-k) : ℂ) = (d : ℂ) ^ (-k) * (M : ℂ) ^ (-k) from
      mul_zpow (d : ℂ) (M : ℂ) (-k)]
  rw [show (((M : ℝ) : ℂ) ^ (k - 1) : ℂ) = (M : ℂ) ^ (k - 1) from by push_cast; rfl]
  rw [show ((M : ℂ) * (τ : ℂ)) ^ (-k) = (M : ℂ) ^ (-k) * (τ : ℂ) ^ (-k) from
      mul_zpow (M : ℂ) (τ : ℂ) (-k)]
  have h_d_combine : (d : ℂ) ^ (k - 1) * (d : ℂ) ^ (-k) = (d : ℂ)⁻¹ := by
    rw [← zpow_add₀ hd_ne, show (k - 1) + (-k) = (-1 : ℤ) from by ring, zpow_neg_one]
  rw [show ⇑g₀ ((Newform.frickeMatrix M : GL (Fin 2) ℝ) • τ) *
        ((d : ℂ) ^ (k - 1) * (M : ℂ) ^ (k - 1)) *
          ((d : ℂ) ^ (-k) * (M : ℂ) ^ (-k) * (τ : ℂ) ^ (-k)) =
      ((d : ℂ) ^ (k - 1) * (d : ℂ) ^ (-k)) *
        (⇑g₀ ((Newform.frickeMatrix M : GL (Fin 2) ℝ) • τ) *
          (M : ℂ) ^ (k - 1) * ((M : ℂ) ^ (-k) * (τ : ℂ) ^ (-k))) from by ring]
  rw [h_d_combine]

/-- **T173 — Unconditional Fricke slash preservation for `cuspFormsOldExtended`.**

`Newform.frickeSlashCuspForm` preserves `cuspFormsOldExtended N k`. This is the
T173 main theorem: the Atkin-Lehner / Fricke involution maps the extended
oldspace `cuspFormsOldExtended N k` (= span of level-raise generators ∪
trivial-inclusion generators per T171) to itself.

Proof: combine the two per-generator residual theorems
`Newform.frickeSlashCuspForm_levelRaise_mem_cuspFormsOldExtended` (Case A:
level-raise generator → trivial-inclusion scaled witness) and
`Newform.frickeSlashCuspForm_levelInclude_cusp_mem_cuspFormsOldExtended`
(Case B: trivial-inclusion generator → level-raise scaled witness) via the
T172 reduction `frickeSlashCuspForm_preserves_cuspFormsOldExtended_iff_on_generators`.

The disjunction `IsOldformGenerator f ∨ IsLevelInclusionOldformGenerator f`
splits into the two cases, each handled by its respective per-generator theorem. -/
theorem Newform.frickeSlashCuspForm_preserves_cuspFormsOldExtended
    {N : ℕ} [NeZero N] {k : ℤ} (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg : g ∈ cuspFormsOldExtended N k) :
    Newform.frickeSlashCuspForm g ∈ cuspFormsOldExtended N k :=
  Newform.frickeSlashCuspForm_preserves_cuspFormsOldExtended_iff_on_generators.mpr
    (fun f h_or => h_or.elim
      (fun h_lr_gen => by
        obtain ⟨M, d, hM_NeZero, hd_NeZero, hd_lt, heq, g₀, h_eq⟩ := h_lr_gen
        haveI := hM_NeZero
        haveI := hd_NeZero
        rw [← h_eq]
        exact Newform.frickeSlashCuspForm_levelRaise_mem_cuspFormsOldExtended
          hd_lt heq g₀)
      (fun h_inc_gen => by
        obtain ⟨M, hM_NeZero, hMN, hMltN, g₀, h_eq⟩ := h_inc_gen
        haveI := hM_NeZero
        rw [← h_eq]
        exact Newform.frickeSlashCuspForm_levelInclude_cusp_mem_cuspFormsOldExtended
          hMN hMltN g₀)) g hg

/-- **T173 — Named Prop form: Fricke preservation on `cuspFormsOldExtended`.**

A named-Prop wrapper around `Newform.frickeSlashCuspForm_preserves_cuspFormsOldExtended`
matching the convention of `Newform.HasFrickeSlashCuspFormPreservesCuspFormsOld`. -/
def Newform.HasFrickeSlashCuspFormPreservesCuspFormsOldExtended
    (N : ℕ) [NeZero N] (k : ℤ) : Prop :=
  ∀ (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
    g ∈ cuspFormsOldExtended N k →
    Newform.frickeSlashCuspForm g ∈ cuspFormsOldExtended N k

/-- **T173 — `HasFrickeSlashCuspFormPreservesCuspFormsOldExtended` holds unconditionally.** -/
theorem Newform.hasFrickeSlashCuspFormPreservesCuspFormsOldExtended
    (N : ℕ) [NeZero N] (k : ℤ) :
    Newform.HasFrickeSlashCuspFormPreservesCuspFormsOldExtended N k :=
  fun g hg => Newform.frickeSlashCuspForm_preserves_cuspFormsOldExtended g hg

/-- **`heckeT_n_cusp k p` preserves `cuspFormsOld N k` at bad primes (T148 helper).**

For the bad-prime case `p ∣ N`, the Hecke operator `heckeT_n_cusp k p` preserves
`cuspFormsOld N k`. Classical proof: reduce to oldform generators
`levelRaise M d k h` (with `d * M = N, d > 1`) and use the level-raise / Hecke
commutativity at the appropriate level.

This claim is **not yet proved** in the present pass. Stated as a named
hypothesis for downstream discharge. The corresponding coprime-prime case is
already proved as `heckeT_n_preserves_cuspFormsOld`; the bad-prime version
requires a generalisation of `heckeT_n_levelRaise_comm` to the
`¬ Nat.Coprime p N` case. -/
def Newform.HasHeckeT_n_cusp_at_divN_PreservesCuspFormsOld
    (N : ℕ) [NeZero N] (k : ℤ) (p : ℕ) [NeZero p]
    (_hp : p.Prime) (_hpN : ¬ Nat.Coprime p N) : Prop :=
  ∀ (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
    g ∈ cuspFormsOld N k → heckeT_n_cusp k p g ∈ cuspFormsOld N k

/-- **`frickeBadAdjointCandidate k p` preserves `cuspFormsOld N k` (T148 helper),
assuming Fricke and bad-prime Hecke each preserve `cuspFormsOld N k`.**

Composing the two preservation properties (Fricke, then T_p, then Fricke)
through the definition `frickeBadAdjointCandidate := frickeSlashCuspForm ∘ₗ
heckeT_n_cusp_lin k p ∘ₗ frickeSlashCuspForm`. -/
lemma Newform.frickeBadAdjointCandidate_preserves_cuspFormsOld
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p]
    {hp : p.Prime} {hpN : ¬ Nat.Coprime p N}
    (h_fricke_old :
      Newform.HasFrickeSlashCuspFormPreservesCuspFormsOld N k)
    (h_T_p_old :
      Newform.HasHeckeT_n_cusp_at_divN_PreservesCuspFormsOld N k p hp hpN)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (hg : g ∈ cuspFormsOld N k) :
    Newform.frickeBadAdjointCandidate k p g ∈ cuspFormsOld N k := by
  rw [Newform.frickeBadAdjointCandidate_apply]
  exact h_fricke_old _ (h_T_p_old _ (h_fricke_old _ hg))

/-! ### Scalar-corrected bad-prime Fricke petN adjoint (T149 audit) -/

/-- **Audit (T149): the T148 candidate `frickeBadAdjointCandidate` is
`W_N · T_p · W_N`, but `W_N⁻¹ = (frickeSquareScalar N k)⁻¹ • W_N` (T144
involution-up-to-scalar).**

The classical Atkin-Lehner adjoint is
`T_p^σ := W_N⁻¹ T_p W_N = (frickeSquareScalar N k)⁻¹ • frickeBadAdjointCandidate`.
This `Newform.frickeBadAdjointCandidateNormalized` packages the scalar-
corrected candidate; it is the operator whose petN identity matches
`petN (T_p f) g = petN f (...)` on the nose, with no extra scalar.

The original `Newform.frickeBadAdjointCandidate` (T148) remains usable but
satisfies the petN identity only up to `frickeSquareScalar N k`. -/
noncomputable def Newform.frickeBadAdjointCandidateNormalized
    {N : ℕ} [NeZero N] (k : ℤ) (p : ℕ) [NeZero p] :
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ]
      CuspForm ((Gamma1 N).map (mapGL ℝ)) k :=
  (Newform.frickeSquareScalar N k)⁻¹ • Newform.frickeBadAdjointCandidate k p

/-- **Underlying-function form of the normalized candidate (T149 helper).** -/
@[simp]
lemma Newform.frickeBadAdjointCandidateNormalized_apply
    {N : ℕ} [NeZero N] (k : ℤ) (p : ℕ) [NeZero p]
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    Newform.frickeBadAdjointCandidateNormalized k p g =
      (Newform.frickeSquareScalar N k)⁻¹ •
        Newform.frickeBadAdjointCandidate k p g := by
  show ((Newform.frickeSquareScalar N k)⁻¹ •
        Newform.frickeBadAdjointCandidate k p) g = _
  rfl

/-- **Named petN adjoint Prop for the normalized bad-prime Fricke candidate
(T149 main reduction)**.

The petN adjoint identity in its scalar-correct form, packaged as a Prop. The
heart of the bad-prime Atkin-Lehner adjoint theorem. -/
def Newform.HasBadPrimeFrickePetNAdjoint
    (N : ℕ) [NeZero N] (k : ℤ) (p : ℕ) [NeZero p] : Prop :=
  ∀ (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
    petN (heckeT_n_cusp k p f) g =
      petN f (Newform.frickeBadAdjointCandidateNormalized k p g)

/-- **Equivalent unnormalized form (T149 helper)**: the petN adjoint Prop for
the original T148 candidate `frickeBadAdjointCandidate` is equivalent to a
`frickeSquareScalar N k`-scaled identity. -/
lemma Newform.hasBadPrimeFrickePetNAdjoint_iff
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p]
    (h_c_ne : Newform.frickeSquareScalar N k ≠ 0) :
    Newform.HasBadPrimeFrickePetNAdjoint N k p ↔
      ∀ (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
        Newform.frickeSquareScalar N k * petN (heckeT_n_cusp k p f) g =
          petN f (Newform.frickeBadAdjointCandidate k p g) := by
  unfold Newform.HasBadPrimeFrickePetNAdjoint
  refine ⟨fun h f g => ?_, fun h f g => ?_⟩
  · rw [h f g, Newform.frickeBadAdjointCandidateNormalized_apply,
      petN_smul_right]
    field_simp
  · rw [Newform.frickeBadAdjointCandidateNormalized_apply, petN_smul_right]
    rw [show (Newform.frickeSquareScalar N k)⁻¹ *
          petN f (Newform.frickeBadAdjointCandidate k p g) =
        (Newform.frickeSquareScalar N k)⁻¹ *
          (Newform.frickeSquareScalar N k * petN (heckeT_n_cusp k p f) g) by
      rw [h f g]]
    field_simp

/-- **Bad-prime newspace preservation, conditional on the scalar-corrected
petN-adjoint identity and oldspace preservation (T149 main).**

For p prime with p ∣ N: the bad-prime Hecke operator `heckeT_n_cusp k p`
preserves `cuspFormsNew N k`, conditional on the named Prop
`Newform.HasBadPrimeFrickePetNAdjoint N k p` and oldspace preservation of the
*normalized* candidate `frickeBadAdjointCandidateNormalized k p`. The
normalized candidate's oldspace preservation reduces to oldspace preservation
of the unnormalized candidate (a scalar multiple is the same submodule
membership). -/
theorem Newform.heckeT_n_cusp_preserves_cuspFormsNew_at_divN_of_normalized_fricke_adjoint
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p] (hp : p.Prime)
    (hpN : ¬ Nat.Coprime p N)
    (h_adj : Newform.HasBadPrimeFrickePetNAdjoint N k p)
    (h_old : ∀ (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
      g ∈ cuspFormsOld N k →
        Newform.frickeBadAdjointCandidateNormalized k p g ∈ cuspFormsOld N k)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (hf : f ∈ cuspFormsNew N k) :
    heckeT_n_cusp k p f ∈ cuspFormsNew N k :=
  heckeT_n_cusp_preserves_cuspFormsNew_at_divN_of_petersson_adjoint hp hpN
    (Newform.frickeBadAdjointCandidateNormalized k p) h_adj h_old f hf

/-- **`frickeBadAdjointCandidateNormalized` preserves cuspFormsOld follows from
unnormalized preservation (T149 helper).** -/
lemma Newform.frickeBadAdjointCandidateNormalized_preserves_cuspFormsOld
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p]
    (h_unnormalized :
      ∀ (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
        g ∈ cuspFormsOld N k →
          Newform.frickeBadAdjointCandidate k p g ∈ cuspFormsOld N k)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (hg : g ∈ cuspFormsOld N k) :
    Newform.frickeBadAdjointCandidateNormalized k p g ∈ cuspFormsOld N k := by
  rw [Newform.frickeBadAdjointCandidateNormalized_apply]
  exact (cuspFormsOld N k).smul_mem _ (h_unnormalized g hg)

/-- **Bad-prime newspace preservation from the three classical inputs (T169
non-overlapping consumer wrapper).**

For `p` prime with `p ∣ N`, the bad-prime Hecke operator `heckeT_n_cusp k p`
preserves `cuspFormsNew N k`, given the **three named classical inputs** that
each correspond to a separate worker lane in the post-T148 chain:

* `h_adj : Newform.HasBadPrimeFrickePetNAdjoint N k p` — the Petersson-level
  bad-prime Atkin-Lehner adjoint identity (the petN-adjoint lane endpoint
  reached from T155 ShiftedFD via T156 → T154-bridge → T153 (→ T160 / T161 /
  T163 / T166) chain).
* `h_fricke_old : Newform.HasFrickeSlashCuspFormPreservesCuspFormsOld N k` —
  the Atkin-Lehner involution preserves the old subspace (oldspace lane H1).
* `h_T_p_old : Newform.HasHeckeT_n_cusp_at_divN_PreservesCuspFormsOld N k p
  hp hpN` — the bad-prime Hecke operator preserves the old subspace
  (oldspace lane H2).

Composes mechanically:

1. `Newform.frickeBadAdjointCandidate_preserves_cuspFormsOld`
   (T148 helper, lines 11209-11219) — combines `h_fricke_old + h_T_p_old`
   into the unnormalized oldspace preservation
   `Newform.frickeBadAdjointCandidate k p g ∈ cuspFormsOld N k`.
2. `Newform.frickeBadAdjointCandidateNormalized_preserves_cuspFormsOld`
   (T149 helper, immediately above) — lifts unnormalized to normalized
   oldspace preservation.
3. `Newform.heckeT_n_cusp_preserves_cuspFormsNew_at_divN_of_normalized_fricke_adjoint`
   (T149 main, line 11297) — combines the petN adjoint `h_adj` with the
   normalized oldspace preservation to conclude bad-prime newspace
   preservation.

This is the **single named consumer endpoint** of the bad-prime newspace
chain: any future worker discharging the three classical inputs (one
petN-adjoint, two oldspace) immediately closes bad-prime newspace
preservation via this theorem with no further plumbing.

References: Diamond–Shurman §5.5.1 (Atkin-Lehner involutions),
§5.6 Prop 5.6.2 (T_p preserves new/old subspaces); Miyake §4.6.5–4.6.6. -/
theorem Newform.heckeT_n_cusp_preserves_cuspFormsNew_at_divN_of_classicalInputs
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p] (hp : p.Prime)
    (hpN : ¬ Nat.Coprime p N)
    (h_adj : Newform.HasBadPrimeFrickePetNAdjoint N k p)
    (h_fricke_old : Newform.HasFrickeSlashCuspFormPreservesCuspFormsOld N k)
    (h_T_p_old : Newform.HasHeckeT_n_cusp_at_divN_PreservesCuspFormsOld N k p hp hpN)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (hf : f ∈ cuspFormsNew N k) :
    heckeT_n_cusp k p f ∈ cuspFormsNew N k :=
  Newform.heckeT_n_cusp_preserves_cuspFormsNew_at_divN_of_normalized_fricke_adjoint
    hp hpN h_adj
    (fun g hg =>
      Newform.frickeBadAdjointCandidateNormalized_preserves_cuspFormsOld
        (fun g' hg' =>
          Newform.frickeBadAdjointCandidate_preserves_cuspFormsOld
            (hp := hp) (hpN := hpN) h_fricke_old h_T_p_old g' hg')
        g hg)
    f hf

/-! ### T174: Extended-oldspace integration of the bad-prime newspace chain

After T171 found that the classical bad-prime preservation is only true at
the *extended* oldspace level (which includes trivial-inclusion generators),
and T173 proved Fricke preservation of `cuspFormsOldExtended` unconditionally,
this section integrates the two live workers (T170: petN-adjoint identity;
T171: Hecke preservation of `cuspFormsOldExtended`) plus the done T173 into
the final bad-prime newspace preservation consumer.

The substantive theorem at the bad-prime case is *only* mathematically true
for `cuspFormsOldExtended` / `cuspFormsNewExtended`. The classical
`cuspFormsNew` (orthogonal of the smaller `cuspFormsOld`) is NOT preserved by
`T_p` at bad primes (e.g., at `N = p²`). -/

/-- **Extended new subspace** — petN-orthogonal of `cuspFormsOldExtended N k`.

Defined as the set of cusp forms orthogonal (w.r.t. `petN`) to every form
in the extended oldspace `cuspFormsOldExtended N k` (= span of all level-raise
generators ∪ trivial-inclusion generators per T171).

Since `cuspFormsOld ⊆ cuspFormsOldExtended`, the extended newspace is a
*sub*module of the classical newspace: `cuspFormsNewExtended ⊆ cuspFormsNew`. -/
def cuspFormsNewExtended (N : ℕ) [NeZero N] (k : ℤ) :
    Submodule ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) where
  carrier := {f | ∀ g, g ∈ cuspFormsOldExtended N k → petN f g = 0}
  zero_mem' g _ := petN_zero_left g
  add_mem' h₁ h₂ g hg := by
    show petN (_ + _) g = 0
    rw [petN_add_left, h₁ g hg, h₂ g hg, add_zero]
  smul_mem' c f hf g hg := by
    show petN (c • f) g = 0
    rw [petN_conj_smul_left, hf g hg, mul_zero]

/-- **`cuspFormsNewExtended ⊆ cuspFormsNew`**: every form orthogonal to the
extended oldspace is in particular orthogonal to the (smaller) classical
oldspace `cuspFormsOld N k`. -/
lemma cuspFormsNewExtended_le_cuspFormsNew {N : ℕ} [NeZero N] {k : ℤ} :
    cuspFormsNewExtended N k ≤ cuspFormsNew N k :=
  fun _ hf g hg => hf g (cuspFormsOld_le_cuspFormsOldExtended hg)

/-- **T140-style strict reducer at the extended level**: for `p ∣ N`, given an
explicit Petersson-adjoint `T_adj` for `T_p` that preserves `cuspFormsOldExtended`,
the bad-prime Hecke operator preserves `cuspFormsNewExtended`. -/
theorem heckeT_n_cusp_preserves_cuspFormsNewExtended_at_divN_of_petersson_adjoint
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p] (hp : p.Prime)
    (hpN : ¬ Nat.Coprime p N)
    (T_adj : CuspForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ]
             CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_adj : ∀ (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
      petN (heckeT_n_cusp k p f) g = petN f (T_adj g))
    (h_old : ∀ (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
      g ∈ cuspFormsOldExtended N k → T_adj g ∈ cuspFormsOldExtended N k)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hf : f ∈ cuspFormsNewExtended N k) :
    heckeT_n_cusp k p f ∈ cuspFormsNewExtended N k := by
  let _ := hp
  let _ := hpN
  intro g hg
  rw [h_adj f g]
  exact hf _ (h_old g hg)

/-- **Bad-prime Hecke preservation of `cuspFormsOldExtended` Prop (T171 territory).**

Companion of `Newform.HasHeckeT_n_cusp_at_divN_PreservesCuspFormsOld` adapted
to the extended oldspace. T171 (Primary's lane) is responsible for proving
this Prop. -/
def Newform.HasHeckeT_n_cusp_at_divN_PreservesCuspFormsOldExtended
    (N : ℕ) [NeZero N] (k : ℤ) (p : ℕ) [NeZero p]
    (_hp : p.Prime) (_hpN : ¬ Nat.Coprime p N) : Prop :=
  ∀ (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
    g ∈ cuspFormsOldExtended N k → heckeT_n_cusp k p g ∈ cuspFormsOldExtended N k

/-- **T171 — trivial-inclusion preservation gap Prop.**

For the level-raise summand `IsOldformGenerator`, T171's
`HasHeckeT_p_divN_LRpd_in_cuspFormsOldExtended_proof` (`p ∣ d` case) and
T168's `heckeT_p_all_levelRaise_comm_divN` (`Coprime p d` case) cover the
cases. For the trivial-inclusion summand `IsLevelInclusionOldformGenerator`,
the remaining gap is preservation of `levelInclude_cusp` images under
`heckeT_n_cusp k p`. This Prop names that gap. -/
def Newform.HasHeckeT_n_cusp_TrivialInclusion_preserves_cuspFormsOldExtended
    (N : ℕ) [NeZero N] (k : ℤ) (p : ℕ) [NeZero p]
    (_hp : Nat.Prime p) (_hpN : ¬ Nat.Coprime p N) : Prop :=
  ∀ (M : ℕ) [NeZero M] (hMN : M ∣ N) (_hMltN : M < N)
    (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k),
    heckeT_n_cusp k p (levelInclude_cusp hMN k g) ∈ cuspFormsOldExtended N k

/-- **T171 — bad-prime Hecke preservation of `cuspFormsOldExtended` (proof).**

Composes the level-raise summand cases (`HasHeckeT_p_divN_LRpd_in_cuspFormsOldExtended_proof`
for `p ∣ d`, `heckeT_p_all_levelRaise_comm_divN` for `Coprime p d`) with
the trivial-inclusion preservation gap Prop. The result instantiates the
public-API Prop `Newform.HasHeckeT_n_cusp_at_divN_PreservesCuspFormsOldExtended`
for downstream T174/T175 consumers. -/
theorem Newform.HasHeckeT_n_cusp_at_divN_PreservesCuspFormsOldExtended_proof
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p]
    (hp : Nat.Prime p) (hpN : ¬ Nat.Coprime p N)
    (h_trivial :
      Newform.HasHeckeT_n_cusp_TrivialInclusion_preserves_cuspFormsOldExtended
        N k p hp hpN) :
    Newform.HasHeckeT_n_cusp_at_divN_PreservesCuspFormsOldExtended N k p hp hpN := by
  intro f hf
  refine Submodule.span_induction
    (p := fun x _ => heckeT_n_cusp k p x ∈ cuspFormsOldExtended N k)
    ?_ ?_ ?_ ?_ hf
  · -- Generator case
    rintro f₀ (⟨M, d, _, _, hd, heq, g, rfl⟩ | ⟨M, _, hMN, hMltN, g, rfl⟩)
    · -- IsOldformGenerator
      by_cases hpd : p ∣ d
      · -- p ∣ d
        exact Newform.HasHeckeT_p_divN_LRpd_in_cuspFormsOldExtended_proof hp hpN
          M d heq hd hpd g
      · -- Coprime p d (since p prime)
        have hpd_cop : Nat.Coprime p d := (hp.coprime_iff_not_dvd).mpr hpd
        rw [heckeT_p_all_levelRaise_comm_divN p hp hpN M d heq hpd_cop g]
        apply cuspFormsOld_le_cuspFormsOldExtended
        refine Submodule.subset_span ?_
        exact ⟨M, d, inferInstance, inferInstance, hd, heq, _, rfl⟩
    · -- IsLevelInclusionOldformGenerator
      exact h_trivial M hMN hMltN g
  · -- Zero
    show heckeT_n_cusp k p (0 : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∈
      cuspFormsOldExtended N k
    rw [heckeT_n_cusp_zero]
    exact (cuspFormsOldExtended N k).zero_mem
  · -- Add
    intros f₁ f₂ _ _ ih₁ ih₂
    show heckeT_n_cusp k p (f₁ + f₂) ∈ cuspFormsOldExtended N k
    rw [heckeT_n_cusp_add]
    exact (cuspFormsOldExtended N k).add_mem ih₁ ih₂
  · -- Smul
    intros c f₁ _ ih
    show heckeT_n_cusp k p (c • f₁) ∈ cuspFormsOldExtended N k
    rw [heckeT_n_cusp_smul]
    exact (cuspFormsOldExtended N k).smul_mem c ih

/-- **T176 — sub-Prop for the `Coprime p M ∧ p*M = N` corner case.**

In the proof of `HasHeckeT_n_cusp_TrivialInclusion_preserves_cuspFormsOldExtended`,
the case-split goes:
- `p ∣ M`: bad-prime case at level `M`, direct via `heckeT_p_all_not_coprime_apply`.
- `Coprime p M ∧ p*M < N`: lift through level `p*M` (also bad-prime).
- `Coprime p M ∧ p*M = N`: requires the `T_p^M = T_p_ut + ⟨p⟩∣α_p` decomposition
  and is genuinely separate. This Prop names that corner case. -/
def Newform.HasHeckeT_n_cusp_TrivialInclusion_preserves_cuspFormsOldExtended_minimal
    (N : ℕ) [NeZero N] (k : ℤ) (p : ℕ) [NeZero p]
    (_hp : Nat.Prime p) (_hpN : ¬ Nat.Coprime p N) : Prop :=
  ∀ (M : ℕ) [NeZero M] (hMN : M ∣ N) (_hMltN : M < N)
    (_hpcop_M : Nat.Coprime p M) (_hpM_eq : p * M = N)
    (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k),
    heckeT_n_cusp k p (levelInclude_cusp hMN k g) ∈ cuspFormsOldExtended N k

/-- **T176 — trivial-inclusion preservation (proof, partial).**

Proves the trivial-inclusion preservation Prop using:
- `p ∣ M`: bad-prime at `M`, direct.
- `Coprime p M ∧ p*M < N`: bad-prime at intermediate level `p*M`.
- `Coprime p M ∧ p*M = N`: dispatched to `_minimal` sub-Prop. -/
theorem Newform.HasHeckeT_n_cusp_TrivialInclusion_preserves_cuspFormsOldExtended_proof
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p]
    (hp : Nat.Prime p) (hpN : ¬ Nat.Coprime p N)
    (h_minimal :
      Newform.HasHeckeT_n_cusp_TrivialInclusion_preserves_cuspFormsOldExtended_minimal
        N k p hp hpN) :
    Newform.HasHeckeT_n_cusp_TrivialInclusion_preserves_cuspFormsOldExtended N k p hp hpN := by
  intro M _ hMN hMltN g
  by_cases hpM : p ∣ M
  · -- Case 1: p ∣ M (bad prime at level M)
    have hpcop_M : ¬ Nat.Coprime p M := fun h => hp.coprime_iff_not_dvd.mp h hpM
    have h_eq : heckeT_n_cusp k p (levelInclude_cusp hMN k g) =
        levelInclude_cusp hMN k (heckeT_n_cusp k p g) := by
      apply CuspForm.ext; intro z
      show (heckeT_n k p (levelInclude_cusp hMN k g).toModularForm').toFun z =
           (heckeT_n k p g.toModularForm').toFun z
      rw [heckeT_n_prime k hp]
      change ⇑((heckeT_p_all k p hp) (levelInclude_cusp hMN k g).toModularForm') z =
             ⇑(heckeT_n k p g.toModularForm') z
      rw [heckeT_n_prime k hp]
      rw [show (⇑((heckeT_p_all k p hp) (levelInclude_cusp hMN k g).toModularForm') :
          UpperHalfPlane → ℂ) = heckeT_p_ut k p hp.pos
            ⇑(levelInclude_cusp hMN k g).toModularForm' from
        heckeT_p_all_not_coprime_apply k hp hpN _]
      rw [show (⇑((heckeT_p_all k p hp) g.toModularForm') :
          UpperHalfPlane → ℂ) = heckeT_p_ut k p hp.pos ⇑g.toModularForm' from
        heckeT_p_all_not_coprime_apply k hp hpcop_M _]
      rfl
    rw [h_eq]
    exact levelInclude_cusp_mem_cuspFormsOldExtended hMN hMltN _
  · -- Case 2: Coprime p M
    have hpcop_M : Nat.Coprime p M := hp.coprime_iff_not_dvd.mpr hpM
    have hp_dvd_N : p ∣ N := by
      by_contra h_ndvd; exact hpN (hp.coprime_iff_not_dvd.mpr h_ndvd)
    have hpM_dvd : p * M ∣ N := hpcop_M.mul_dvd_of_dvd_of_dvd hp_dvd_N hMN
    by_cases hpM_lt : p * M < N
    · -- Case 2a: p*M < N. Use intermediate level p*M (bad-prime case there).
      haveI : NeZero (p * M) := ⟨Nat.mul_ne_zero hp.ne_zero (NeZero.ne M)⟩
      have hM_dvd_pM : M ∣ p * M := Dvd.intro_left p rfl
      have hpcop_pM : ¬ Nat.Coprime p (p * M) := fun h =>
        hp.coprime_iff_not_dvd.mp h ⟨M, rfl⟩
      have h_eq : heckeT_n_cusp k p (levelInclude_cusp hMN k g) =
          levelInclude_cusp hpM_dvd k
            (heckeT_n_cusp k p (levelInclude_cusp hM_dvd_pM k g)) := by
        apply CuspForm.ext; intro z
        show (heckeT_n k p (levelInclude_cusp hMN k g).toModularForm').toFun z =
             (heckeT_n k p (levelInclude_cusp hM_dvd_pM k g).toModularForm').toFun z
        rw [heckeT_n_prime k hp]
        change ⇑((heckeT_p_all k p hp) (levelInclude_cusp hMN k g).toModularForm') z =
               ⇑(heckeT_n k p (levelInclude_cusp hM_dvd_pM k g).toModularForm') z
        rw [heckeT_n_prime k hp]
        rw [show (⇑((heckeT_p_all k p hp) (levelInclude_cusp hMN k g).toModularForm') :
            UpperHalfPlane → ℂ) = heckeT_p_ut k p hp.pos
              ⇑(levelInclude_cusp hMN k g).toModularForm' from
          heckeT_p_all_not_coprime_apply k hp hpN _]
        rw [show (⇑((heckeT_p_all k p hp) (levelInclude_cusp hM_dvd_pM k g).toModularForm') :
            UpperHalfPlane → ℂ) = heckeT_p_ut k p hp.pos
              ⇑(levelInclude_cusp hM_dvd_pM k g).toModularForm' from
          heckeT_p_all_not_coprime_apply k hp hpcop_pM _]
        rfl
      rw [h_eq]
      exact levelInclude_cusp_mem_cuspFormsOldExtended hpM_dvd hpM_lt _
    · -- Case 2b: p*M = N. Dispatch to _minimal sub-Prop.
      push_neg at hpM_lt
      have hpM_eq : p * M = N := le_antisymm
        (Nat.le_of_dvd (NeZero.pos N) hpM_dvd) hpM_lt
      exact h_minimal M hMN hMltN hpcop_M hpM_eq g

/-- **T177 — slash by `T_p_lower` reduces to a level-raise scalar.**

For `Coprime p M` and any cusp form `g : CuspForm Γ₁(M) k`, the slash of
the diamond image by `T_p_lower` equals `(p:ℂ)^(k-1) • LR_p(⟨p⟩ g)` at
every point on `ℍ`.  Bridges:
1. Slash via `(T_p_lower : GL ℚ)` ≡ slash via `glMap T_p_lower` (definitional via
   `monoidHomSlashAction glMap` instance).
2. `glMap (T_p_lower p hp)` equals `levelRaiseMatrix p` as `GL (Fin 2) ℝ`
   (both have matrix `!![p, 0; 0, 1]` over ℝ).
3. Slash by `levelRaiseMatrix p` reduces via `slash_apply` and the
   `σ/det/denom` helpers.
4. `levelRaiseFun_apply` rewrites the result as `⇑D (α_p • z)`.
5. Defeq bridge `⇑(diamondOp_cusp k a g) = ⇑(diamondOp k a g.toModularForm')`. -/
private lemma diamondOp_slash_T_p_lower_apply
    {M : ℕ} [NeZero M] {k : ℤ} {p : ℕ} [NeZero p]
    (hp : Nat.Prime p) (hpcop : Nat.Coprime p M)
    (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) (z : UpperHalfPlane) :
    (⇑(diamondOp k (ZMod.unitOfCoprime p hpcop) g.toModularForm') ∣[k]
        (T_p_lower p hp.pos : GL (Fin 2) ℚ)) z =
      ((p : ℂ) ^ (k - 1)) * ⇑(levelRaise M p k
        (diamondOp_cusp k (ZMod.unitOfCoprime p hpcop) g)) z := by
  -- Bridge T_p_lower (ℚ) → levelRaiseMatrix p (ℝ)
  have h_glMap_eq : (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) = levelRaiseMatrix p := by
    apply Units.ext
    ext i j
    show ((T_p_lower p hp.pos : Matrix (Fin 2) (Fin 2) ℚ).map
          (algebraMap ℚ ℝ)) i j =
         (!![(p : ℝ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) i j
    rw [T_p_lower_coe]
    fin_cases i
    · fin_cases j
      · show ((p : ℚ) : ℝ) = (p : ℝ); norm_num
      · show ((0 : ℚ) : ℝ) = 0; norm_num
    · fin_cases j
      · show ((0 : ℚ) : ℝ) = 0; norm_num
      · show ((1 : ℚ) : ℝ) = (1 : ℝ); norm_num
  -- Convert ℚ slash to ℝ slash via SlashAction definitional equality
  show (⇑(diamondOp k (ZMod.unitOfCoprime p hpcop) g.toModularForm') ∣[k]
        glMap (T_p_lower p hp.pos)) z = _
  rw [h_glMap_eq]
  -- Apply slash formula for levelRaiseMatrix p
  rw [ModularForm.slash_apply, σ_levelRaiseMatrix, RingHom.id_apply,
      abs_levelRaiseMatrix_det_val, denom_levelRaiseMatrix, one_zpow, mul_one]
  -- Replace LR_p ⟨p⟩ g via levelRaiseFun_apply
  have h_LR_apply : ⇑(levelRaise M p k
        (diamondOp_cusp k (ZMod.unitOfCoprime p hpcop) g)) z =
      ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpcop) g) (levelRaiseMatrix p • z) := by
    show levelRaiseFun p k ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpcop) g) z = _
    rw [levelRaiseFun_apply]
  rw [h_LR_apply]
  -- Bridge ⇑(diamondOp_cusp ...) = ⇑(diamondOp ...) (defeq)
  show ⇑(diamondOp k (ZMod.unitOfCoprime p hpcop) g.toModularForm')
        (levelRaiseMatrix p • z) * ((p : ℝ) ^ (k - 1) : ℂ) =
      (p : ℂ) ^ (k - 1) *
        ⇑(diamondOp k (ZMod.unitOfCoprime p hpcop) g.toModularForm')
          (levelRaiseMatrix p • z)
  rw [show ((p : ℝ) ^ (k - 1) : ℂ) = (p : ℂ) ^ (k - 1) from by push_cast; rfl]
  ring

/-- **T177 — minimal corner case proof.**

Proves `Newform.HasHeckeT_n_cusp_TrivialInclusion_preserves_cuspFormsOldExtended_minimal`
via the function-level decomposition:
```
heckeT_n_cusp k p (levelInclude_cusp hMN k g) =
  levelInclude_cusp hMN k (heckeT_n_cusp k p g) -
    (p:ℂ)^(k-1) • levelRaise M p k (⟨p⟩ g)
```
where the first RHS term is in `cuspFormsOldExtended` via `levelInclude_cusp_mem`,
and the second RHS term is in `cuspFormsOld ⊆ cuspFormsOldExtended` via
`IsOldformGenerator` (since `p * M = N`). -/
theorem Newform.HasHeckeT_n_cusp_TrivialInclusion_preserves_cuspFormsOldExtended_minimal_proof
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p]
    (hp : Nat.Prime p) (hpN : ¬ Nat.Coprime p N) :
    Newform.HasHeckeT_n_cusp_TrivialInclusion_preserves_cuspFormsOldExtended_minimal
      N k p hp hpN := by
  intro M _ hMN hMltN hpcop_M hpM_eq g
  subst hpM_eq
  set a : (ZMod M)ˣ := ZMod.unitOfCoprime p hpcop_M with ha_def
  set D : CuspForm ((Gamma1 M).map (mapGL ℝ)) k := diamondOp_cusp k a g with hD_def
  set LR_p_D : CuspForm ((Gamma1 (p * M)).map (mapGL ℝ)) k :=
    levelRaise M p k D with hLR_def
  have h_eq : heckeT_n_cusp k p (levelInclude_cusp hMN k g) =
      levelInclude_cusp hMN k (heckeT_n_cusp k p g) -
      ((p : ℂ) ^ (k - 1)) • LR_p_D := by
    apply CuspForm.ext; intro z
    -- Unfold LHS to heckeT_p_ut k p hp.pos ⇑g z (since p ∣ p*M, bad-prime case at p*M)
    have h_LHS :
        (heckeT_n_cusp k p (levelInclude_cusp hMN k g) : CuspForm _ _) z =
        heckeT_p_ut k p hp.pos ⇑g z := by
      show (heckeT_n k p (levelInclude_cusp hMN k g).toModularForm').toFun z = _
      rw [heckeT_n_prime k hp]
      change ⇑((heckeT_p_all k p hp) (levelInclude_cusp hMN k g).toModularForm') z = _
      rw [heckeT_p_all_not_coprime_apply k hp hpN _]
      rfl
    -- Decompose ⇑(heckeT_n_cusp k p g) z via heckeT_p_fun (Coprime p M case)
    have h_T_M_apply :
        (heckeT_n_cusp k p g : CuspForm _ _) z =
        heckeT_p_ut k p hp.pos ⇑g z +
          ((⇑(diamondOp k a g.toModularForm') ∣[k]
            (T_p_lower p hp.pos : GL (Fin 2) ℚ)) z) := by
      show (heckeT_n k p g.toModularForm').toFun z = _
      rw [heckeT_n_prime k hp, heckeT_p_all_coprime k hp hpcop_M]
      rfl
    -- Slash-by-T_p_lower bridge
    have h_slash :
        (⇑(diamondOp k a g.toModularForm') ∣[k]
          (T_p_lower p hp.pos : GL (Fin 2) ℚ)) z =
        ((p : ℂ) ^ (k - 1)) * ⇑LR_p_D z :=
      diamondOp_slash_T_p_lower_apply hp hpcop_M g z
    -- Now combine
    rw [h_LHS]
    -- RHS: (levelInclude_cusp hMN k (heckeT_n_cusp k p g) - ((p:ℂ)^(k-1)) • LR_p_D) z
    -- Step: (f - g) z = f z - g z, levelInclude_cusp_coe rfl, smul.
    show heckeT_p_ut k p hp.pos ⇑g z =
         (levelInclude_cusp hMN k (heckeT_n_cusp k p g)) z -
         ((p : ℂ) ^ (k - 1) • LR_p_D) z
    show heckeT_p_ut k p hp.pos ⇑g z =
         (heckeT_n_cusp k p g) z -
         (p : ℂ) ^ (k - 1) * (LR_p_D : CuspForm _ _) z
    rw [h_T_M_apply, h_slash]
    ring
  rw [h_eq]
  apply Submodule.sub_mem
  · exact levelInclude_cusp_mem_cuspFormsOldExtended hMN hMltN _
  · apply Submodule.smul_mem
    apply cuspFormsOld_le_cuspFormsOldExtended
    refine Submodule.subset_span ?_
    refine ⟨M, p, inferInstance, inferInstance, hp.one_lt, rfl, D, ?_⟩
    rfl

/-- **T177 — Trivial-inclusion preservation, unconditional.**

Combines `_proof` (T176, the case-split scaffold) with `_minimal_proof`
(T177, the corner case) to obtain the unconditional trivial-inclusion
preservation. -/
theorem Newform.HasHeckeT_n_cusp_TrivialInclusion_preserves_cuspFormsOldExtended_unconditional
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p]
    (hp : Nat.Prime p) (hpN : ¬ Nat.Coprime p N) :
    Newform.HasHeckeT_n_cusp_TrivialInclusion_preserves_cuspFormsOldExtended N k p hp hpN :=
  Newform.HasHeckeT_n_cusp_TrivialInclusion_preserves_cuspFormsOldExtended_proof hp hpN
    (Newform.HasHeckeT_n_cusp_TrivialInclusion_preserves_cuspFormsOldExtended_minimal_proof
      hp hpN)

/-- **T177 — Bad-prime Hecke preservation of `cuspFormsOldExtended`, unconditional.**

Combines T171's conditional package with T177's unconditional trivial-inclusion
preservation, instantiating the public-API Prop unconditionally. -/
theorem Newform.HasHeckeT_n_cusp_at_divN_PreservesCuspFormsOldExtended_unconditional
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p]
    (hp : Nat.Prime p) (hpN : ¬ Nat.Coprime p N) :
    Newform.HasHeckeT_n_cusp_at_divN_PreservesCuspFormsOldExtended N k p hp hpN :=
  Newform.HasHeckeT_n_cusp_at_divN_PreservesCuspFormsOldExtended_proof hp hpN
    (Newform.HasHeckeT_n_cusp_TrivialInclusion_preserves_cuspFormsOldExtended_unconditional
      hp hpN)

/-- **Extended companion: `frickeBadAdjointCandidate k p` preserves
`cuspFormsOldExtended`** assuming Fricke and bad-prime Hecke each preserve it.

Composition: `frickeBadAdjointCandidate := frickeSlash ∘ T_p ∘ frickeSlash`,
each step preserving `cuspFormsOldExtended`. -/
lemma Newform.frickeBadAdjointCandidate_preserves_cuspFormsOldExtended
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p]
    {hp : p.Prime} {hpN : ¬ Nat.Coprime p N}
    (h_fricke_old :
      Newform.HasFrickeSlashCuspFormPreservesCuspFormsOldExtended N k)
    (h_T_p_old :
      Newform.HasHeckeT_n_cusp_at_divN_PreservesCuspFormsOldExtended N k p hp hpN)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg : g ∈ cuspFormsOldExtended N k) :
    Newform.frickeBadAdjointCandidate k p g ∈ cuspFormsOldExtended N k := by
  rw [Newform.frickeBadAdjointCandidate_apply]
  exact h_fricke_old _ (h_T_p_old _ (h_fricke_old _ hg))

/-- **Extended companion: `frickeBadAdjointCandidateNormalized` preserves
`cuspFormsOldExtended` from unnormalized preservation.** -/
lemma Newform.frickeBadAdjointCandidateNormalized_preserves_cuspFormsOldExtended
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p]
    (h_unnormalized :
      ∀ (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
        g ∈ cuspFormsOldExtended N k →
          Newform.frickeBadAdjointCandidate k p g ∈ cuspFormsOldExtended N k)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg : g ∈ cuspFormsOldExtended N k) :
    Newform.frickeBadAdjointCandidateNormalized k p g ∈
        cuspFormsOldExtended N k := by
  rw [Newform.frickeBadAdjointCandidateNormalized_apply]
  exact (cuspFormsOldExtended N k).smul_mem _ (h_unnormalized g hg)

/-- **T149-style extended consumer**: bad-prime newspace-extended preservation
from the petN-adjoint identity and oldspace-extended preservation of the
*normalized* candidate. -/
theorem Newform.heckeT_n_cusp_preserves_cuspFormsNewExtended_at_divN_of_normalized_fricke_adjoint
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p] (hp : p.Prime)
    (hpN : ¬ Nat.Coprime p N)
    (h_adj : Newform.HasBadPrimeFrickePetNAdjoint N k p)
    (h_old : ∀ (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
      g ∈ cuspFormsOldExtended N k →
        Newform.frickeBadAdjointCandidateNormalized k p g ∈
            cuspFormsOldExtended N k)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hf : f ∈ cuspFormsNewExtended N k) :
    heckeT_n_cusp k p f ∈ cuspFormsNewExtended N k :=
  heckeT_n_cusp_preserves_cuspFormsNewExtended_at_divN_of_petersson_adjoint
    hp hpN
    (Newform.frickeBadAdjointCandidateNormalized k p) h_adj h_old f hf

/-- **T148/T174 final consumer (extended)**: bad-prime Hecke preservation
of `cuspFormsNewExtended` from the three classical inputs at the *extended*
level.

This is the integration endpoint of the bad-prime newspace chain after
T170/T171/T173. It consumes:
* `h_adj : HasBadPrimeFrickePetNAdjoint N k p` — **T170 territory** (live).
* `h_fricke_old : HasFrickeSlashCuspFormPreservesCuspFormsOldExtended N k` —
  **T173 (DONE)**: see `Newform.hasFrickeSlashCuspFormPreservesCuspFormsOldExtended`.
* `h_T_p_old : HasHeckeT_n_cusp_at_divN_PreservesCuspFormsOldExtended` —
  **T171 territory** (live).

Once T170 and T171 land, this theorem yields the unconditional bad-prime
newspace preservation for the (mathematically correct) extended newspace. -/
theorem Newform.heckeT_n_cusp_preserves_cuspFormsNewExtended_at_divN_of_classicalInputs
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p] (hp : p.Prime)
    (hpN : ¬ Nat.Coprime p N)
    (h_adj : Newform.HasBadPrimeFrickePetNAdjoint N k p)
    (h_fricke_old :
      Newform.HasFrickeSlashCuspFormPreservesCuspFormsOldExtended N k)
    (h_T_p_old :
      Newform.HasHeckeT_n_cusp_at_divN_PreservesCuspFormsOldExtended N k p hp hpN)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hf : f ∈ cuspFormsNewExtended N k) :
    heckeT_n_cusp k p f ∈ cuspFormsNewExtended N k :=
  Newform.heckeT_n_cusp_preserves_cuspFormsNewExtended_at_divN_of_normalized_fricke_adjoint
    hp hpN h_adj
    (fun g hg =>
      Newform.frickeBadAdjointCandidateNormalized_preserves_cuspFormsOldExtended
        (fun g' hg' =>
          Newform.frickeBadAdjointCandidate_preserves_cuspFormsOldExtended
            (hp := hp) (hpN := hpN) h_fricke_old h_T_p_old g' hg')
        g hg)
    f hf

/-- **T174 streamlined endpoint**: bad-prime newspace-extended preservation
reduced to *exactly* T170 + T171.

Since T173 (`HasFrickeSlashCuspFormPreservesCuspFormsOldExtended`) is
unconditional via `Newform.hasFrickeSlashCuspFormPreservesCuspFormsOldExtended`,
the final consumer needs only the two live dependencies — T170's petN-adjoint
identity and T171's extended-oldspace Hecke preservation.

This is the **single named consumer endpoint** of the post-T173 bad-prime
newspace chain. -/
theorem Newform.heckeT_n_cusp_preserves_cuspFormsNewExtended_at_divN_of_T170_T171
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p] (hp : p.Prime)
    (hpN : ¬ Nat.Coprime p N)
    (h_adj : Newform.HasBadPrimeFrickePetNAdjoint N k p)
    (h_T_p_old :
      Newform.HasHeckeT_n_cusp_at_divN_PreservesCuspFormsOldExtended N k p hp hpN)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hf : f ∈ cuspFormsNewExtended N k) :
    heckeT_n_cusp k p f ∈ cuspFormsNewExtended N k :=
  Newform.heckeT_n_cusp_preserves_cuspFormsNewExtended_at_divN_of_classicalInputs
    hp hpN h_adj
    (Newform.hasFrickeSlashCuspFormPreservesCuspFormsOldExtended N k)
    h_T_p_old f hf

/-! ### T175: Downstream extended-newspace API for the SMO route

After T174 lifted bad-prime preservation to `cuspFormsNewExtended`, this
section provides the downstream API needed for the strong multiplicity one
route at the *extended* level: `IsInNewSubspaceExtended`, the disjointness of
extended old/new, and `IsNewformExtended` / `NewformExtended` — analogues of
the existing `IsInNewSubspace`, `cuspFormsOld_disjoint_cuspFormsNew`,
`IsNewform`, and `Newform N k` structures, but using the (mathematically
correct) extended subspaces.

The classical narrow `Newform N k` structure (defined via `cuspFormsNew`)
remains the standard handle for downstream code; `NewformExtended` is
strictly stronger (every `NewformExtended` is in particular a `Newform`,
since `cuspFormsNewExtended ⊆ cuspFormsNew`). For the bad-prime preservation
side of the SMO route, downstream consumers should require the stronger
`NewformExtended` hypothesis. -/

/-- A cusp form is in the **extended new subspace** if it is orthogonal
(w.r.t. `petN`) to every form in `cuspFormsOldExtended N k` (i.e., every
level-raise generator AND every trivial-inclusion generator).

Strictly stronger than `IsInNewSubspace` (which only requires orthogonality
to level-raise generators). -/
def IsInNewSubspaceExtended (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : Prop :=
  ∀ g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
    g ∈ cuspFormsOldExtended N k → petN f g = 0

/-- `IsInNewSubspaceExtended f ↔ f ∈ cuspFormsNewExtended N k`. -/
lemma isInNewSubspaceExtended_iff_mem (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    IsInNewSubspaceExtended f ↔ f ∈ cuspFormsNewExtended N k :=
  Iff.rfl

/-- `IsInNewSubspaceExtended → IsInNewSubspace`: orthogonality to the *extended*
oldspace implies orthogonality to the (smaller) classical oldspace. -/
lemma IsInNewSubspaceExtended.isInNewSubspace
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (h : IsInNewSubspaceExtended f) :
    IsInNewSubspace f :=
  fun g hg => h g (cuspFormsOld_le_cuspFormsOldExtended hg)

/-- The intersection of `cuspFormsOldExtended` and `cuspFormsNewExtended`
is trivial. Mirrors `cuspFormsOld_disjoint_cuspFormsNew`.

If `f ∈ cuspFormsOldExtended ∩ cuspFormsNewExtended`, then `f ∈ cuspFormsNewExtended`
means `petN f g = 0` for all `g ∈ cuspFormsOldExtended`. Taking `g = f`, we get
`petN f f = 0`, hence `f = 0` by `petN_definite`. -/
theorem cuspFormsOldExtended_disjoint_cuspFormsNewExtended
    {N : ℕ} [NeZero N] {k : ℤ} :
    Disjoint (cuspFormsOldExtended N k) (cuspFormsNewExtended N k) := by
  rw [Submodule.disjoint_def]
  intro f hf_old hf_new
  exact petN_definite f (hf_new f hf_old)

/-- The classical `cuspFormsNew_disjoint`-style result follows for free at the
extended level too: extended new is disjoint from the larger extended old. -/
theorem cuspFormsOldExtended_disjoint_cuspFormsNew
    {N : ℕ} [NeZero N] {k : ℤ} :
    Disjoint (cuspFormsOldExtended N k) (cuspFormsNewExtended N k) :=
  cuspFormsOldExtended_disjoint_cuspFormsNewExtended

/-- **`IsNewformExtended` predicate (T175 downstream).**

A cusp form is an *extended newform* if it is a common Hecke eigenform, lies
in the *extended* new subspace `cuspFormsNewExtended`, and is normalised
(`a_1 = 1`).  Strictly stronger than `IsNewform` (which uses the smaller
classical `cuspFormsNew`). The bad-prime Hecke preservation only holds for
the extended newspace, so downstream SMO consumers requiring full Hecke
stability should use `IsNewformExtended`. -/
structure IsNewformExtended (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : Prop where
  isEigen : IsEigenform f
  isNew : f ∈ cuspFormsNewExtended N k
  isNorm : (ModularFormClass.qExpansion (1 : ℝ) f).coeff 1 = 1

/-- An extended newform is in particular a (classical) newform.

Since `cuspFormsNewExtended ⊆ cuspFormsNew`, the membership is preserved.
Eigenform and normalisation conditions transfer directly. -/
theorem IsNewformExtended.isNewform
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (h : IsNewformExtended f) : IsNewform f where
  isEigen := h.isEigen
  isNew := cuspFormsNewExtended_le_cuspFormsNew h.isNew
  isNorm := h.isNorm

/-- **`NewformExtended` structure (T175 downstream).**

Bundled extended newform: an `Eigenform` together with extended-newspace
membership and normalisation. Strictly stronger than `Newform N k` (every
`NewformExtended` gives a `Newform` via the inclusion `cuspFormsNewExtended ⊆
cuspFormsNew`).

The bad-prime Hecke preservation (T174) operates at this strengthened
level, so SMO downstream consumers requiring unconditional Hecke stability
should use `NewformExtended`. -/
structure NewformExtended (N : ℕ) [NeZero N] (k : ℤ)
    extends Eigenform N k where
  /-- The form is in the *extended* new subspace `cuspFormsNewExtended`. -/
  isNew : toCuspForm ∈ cuspFormsNewExtended N k
  /-- Normalisation at the canonical Fourier period: the first Fourier
  coefficient is `1`. -/
  isNorm : (ModularFormClass.qExpansion (1 : ℝ) toCuspForm).coeff 1 = 1

/-- A `NewformExtended` satisfies `IsNewformExtended`. -/
theorem NewformExtended.isNewformExtended (f : NewformExtended N k) :
    IsNewformExtended f.toCuspForm where
  isEigen := f.toEigenform.isEigenform
  isNew := f.isNew
  isNorm := f.isNorm

/-- Every `NewformExtended` gives a (classical) `Newform`.

Combines the structure projections with the inclusion
`cuspFormsNewExtended ⊆ cuspFormsNew`. -/
def NewformExtended.toNewform (f : NewformExtended N k) : Newform N k where
  toEigenform := f.toEigenform
  isNew := cuspFormsNewExtended_le_cuspFormsNew f.isNew
  isNorm := f.isNorm

/-- **T175: Combined Hecke preservation through `cuspFormsNew` for an extended
newform.**

For `f ∈ cuspFormsNewExtended` and *any* prime `p`, the bad-prime Hecke
operator `heckeT_n_cusp k p f` lies in the (classical) `cuspFormsNew N k`,
provided either `(p, N) = 1` (coprime, no extra hypotheses needed) or
`p ∣ N` and the T170+T171 conditions hold.

This is the **integration endpoint** for the SMO downstream chain combining:
* the existing classical-coprime `heckeT_n_preserves_cuspFormsNew`
  (`Nat.Coprime p N`), and
* the T174 extended-bad-prime
  `heckeT_n_cusp_preserves_cuspFormsNewExtended_at_divN_of_T170_T171`
  combined with `cuspFormsNewExtended ⊆ cuspFormsNew`.

The conclusion is in (classical) `cuspFormsNew`, not `cuspFormsNewExtended`,
because the coprime case lifts directly via the existing classical preservation;
this is sufficient for SMO consumers that operate at the classical
`cuspFormsNew` level. For the strictly extended conclusion, use
`heckeT_n_cusp_preserves_cuspFormsNewExtended_at_divN_of_T170_T171` directly. -/
theorem heckeT_n_cusp_preserves_cuspFormsNew_of_NewformExtended_at_divN
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p] (hp : p.Prime)
    (hpN : ¬ Nat.Coprime p N)
    (h_adj : Newform.HasBadPrimeFrickePetNAdjoint N k p)
    (h_T_p_old :
      Newform.HasHeckeT_n_cusp_at_divN_PreservesCuspFormsOldExtended N k p hp hpN)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hf : f ∈ cuspFormsNewExtended N k) :
    heckeT_n_cusp k p f ∈ cuspFormsNew N k :=
  cuspFormsNewExtended_le_cuspFormsNew
    (Newform.heckeT_n_cusp_preserves_cuspFormsNewExtended_at_divN_of_T170_T171
      hp hpN h_adj h_T_p_old f hf)

/-! ### T178: Post-T177 strictly-lower consumers (T170-only)

After T177 made `Newform.HasHeckeT_n_cusp_at_divN_PreservesCuspFormsOldExtended`
unconditional via
`Newform.HasHeckeT_n_cusp_at_divN_PreservesCuspFormsOldExtended_unconditional`,
the consumer endpoints `..._of_T170_T171` no longer need the T171 hypothesis
explicitly; they reduce to taking only the petN-adjoint identity (T170).

These wrappers expose the strictly-lower consumer signatures so downstream
callers requiring bad-prime newspace preservation no longer need to thread
the T171 input. The single remaining theorem to make these unconditional is
`Newform.HasBadPrimeFrickePetNAdjoint N k p` (T170 territory). -/

/-- **T178 — bad-prime newspace-extended preservation, T170-only.**

Strictly-lower consumer of
`Newform.heckeT_n_cusp_preserves_cuspFormsNewExtended_at_divN_of_T170_T171`:
since T177 makes the T171 input unconditional, this theorem drops `h_T_p_old`
and takes only the petN-adjoint identity `h_adj : HasBadPrimeFrickePetNAdjoint`.

Single remaining input for unconditional bad-prime newspace-extended
preservation: `Newform.HasBadPrimeFrickePetNAdjoint N k p` (T170 territory). -/
theorem Newform.heckeT_n_cusp_preserves_cuspFormsNewExtended_at_divN_of_T170
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p] (hp : p.Prime)
    (hpN : ¬ Nat.Coprime p N)
    (h_adj : Newform.HasBadPrimeFrickePetNAdjoint N k p)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hf : f ∈ cuspFormsNewExtended N k) :
    heckeT_n_cusp k p f ∈ cuspFormsNewExtended N k :=
  Newform.heckeT_n_cusp_preserves_cuspFormsNewExtended_at_divN_of_T170_T171
    hp hpN h_adj
    (Newform.HasHeckeT_n_cusp_at_divN_PreservesCuspFormsOldExtended_unconditional
      hp hpN)
    f hf

/-- **T178 — Newform-extended classical-newspace consumer, T170-only.**

Strictly-lower consumer of
`heckeT_n_cusp_preserves_cuspFormsNew_of_NewformExtended_at_divN`:
since T177 makes the T171 input unconditional, this theorem drops `h_T_p_old`
and takes only the petN-adjoint identity. The conclusion is in the classical
`cuspFormsNew N k` (sufficient for SMO consumers operating at the classical level). -/
theorem heckeT_n_cusp_preserves_cuspFormsNew_of_NewformExtended_at_divN_of_T170
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p] (hp : p.Prime)
    (hpN : ¬ Nat.Coprime p N)
    (h_adj : Newform.HasBadPrimeFrickePetNAdjoint N k p)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hf : f ∈ cuspFormsNewExtended N k) :
    heckeT_n_cusp k p f ∈ cuspFormsNew N k :=
  cuspFormsNewExtended_le_cuspFormsNew
    (Newform.heckeT_n_cusp_preserves_cuspFormsNewExtended_at_divN_of_T170
      hp hpN h_adj f hf)

/-- **T178 — final extended consumer, T170-only (T173 + T177 already
discharged).**

Strictly-lower consumer of
`Newform.heckeT_n_cusp_preserves_cuspFormsNewExtended_at_divN_of_classicalInputs`:
T173 (`HasFrickeSlashCuspFormPreservesCuspFormsOldExtended`) is unconditional
via `Newform.hasFrickeSlashCuspFormPreservesCuspFormsOldExtended`, and T177
(via `_unconditional`) makes T171 unconditional. So the only remaining
hypothesis is the petN-adjoint identity (T170). -/
theorem Newform.heckeT_n_cusp_preserves_cuspFormsNewExtended_at_divN_of_classicalInputs_T170_only
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p] (hp : p.Prime)
    (hpN : ¬ Nat.Coprime p N)
    (h_adj : Newform.HasBadPrimeFrickePetNAdjoint N k p)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hf : f ∈ cuspFormsNewExtended N k) :
    heckeT_n_cusp k p f ∈ cuspFormsNewExtended N k :=
  Newform.heckeT_n_cusp_preserves_cuspFormsNewExtended_at_divN_of_classicalInputs
    hp hpN h_adj
    (Newform.hasFrickeSlashCuspFormPreservesCuspFormsOldExtended N k)
    (Newform.HasHeckeT_n_cusp_at_divN_PreservesCuspFormsOldExtended_unconditional
      hp hpN)
    f hf

/-! ### T179: SMO downstream — unified Hecke consumer at all primes

Building on the T178 strictly-lower consumers (post-T177 T171 unconditional),
this section provides:
* unconditional unconditional `frickeBadAdjointCandidate` preservation lemmas;
* a unified `cuspFormsNew` Hecke-stability statement for `f ∈ cuspFormsNewExtended`
  covering *every prime* `p`, conditional only on T170 at bad primes;
* `NewformExtended`-level convenience wrappers;
* a dependency-audit theorem documenting the post-T177 SMO route status. -/

/-- **T179: `frickeBadAdjointCandidate` preserves `cuspFormsOldExtended`
unconditionally.**

T173 makes `HasFrickeSlashCuspFormPreservesCuspFormsOldExtended` unconditional;
T177 makes `HasHeckeT_n_cusp_at_divN_PreservesCuspFormsOldExtended` unconditional.
The T148 helper composing these closes the Fricke-bad adjoint candidate's
preservation of `cuspFormsOldExtended` without any hypothesis. -/
lemma Newform.frickeBadAdjointCandidate_preserves_cuspFormsOldExtended_unconditional
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p]
    (hp : p.Prime) (hpN : ¬ Nat.Coprime p N)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg : g ∈ cuspFormsOldExtended N k) :
    Newform.frickeBadAdjointCandidate k p g ∈ cuspFormsOldExtended N k :=
  Newform.frickeBadAdjointCandidate_preserves_cuspFormsOldExtended
    (hp := hp) (hpN := hpN)
    (Newform.hasFrickeSlashCuspFormPreservesCuspFormsOldExtended N k)
    (Newform.HasHeckeT_n_cusp_at_divN_PreservesCuspFormsOldExtended_unconditional
      hp hpN)
    g hg

/-- **T179: `frickeBadAdjointCandidateNormalized` preserves `cuspFormsOldExtended`
unconditionally.**

The `frickeSquareScalar`-normalized variant of the bad-prime Fricke adjoint
candidate, with unconditional oldspace-extended preservation derived from the
unnormalized version. -/
lemma Newform.frickeBadAdjointCandidateNormalized_preserves_cuspFormsOldExtended_unconditional
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p]
    (hp : p.Prime) (hpN : ¬ Nat.Coprime p N)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg : g ∈ cuspFormsOldExtended N k) :
    Newform.frickeBadAdjointCandidateNormalized k p g ∈
        cuspFormsOldExtended N k :=
  Newform.frickeBadAdjointCandidateNormalized_preserves_cuspFormsOldExtended
    (fun g' hg' =>
      Newform.frickeBadAdjointCandidate_preserves_cuspFormsOldExtended_unconditional
        hp hpN g' hg')
    g hg

/-- **T179 unified prime Hecke consumer**: for `f ∈ cuspFormsNewExtended`, the
Hecke operator `heckeT_n_cusp k p f` lies in (classical) `cuspFormsNew N k`
for **every prime `p`**, with T170 needed only at bad primes.

Combines:
* The classical coprime case `heckeT_n_preserves_cuspFormsNew` (`Nat.Coprime p N`),
  applied via `cuspFormsNewExtended ⊆ cuspFormsNew`.
* The post-T177/T178 bad-prime consumer
  `heckeT_n_cusp_preserves_cuspFormsNew_of_NewformExtended_at_divN_of_T170`
  (`¬ Nat.Coprime p N`), needing T170 only.

The hypothesis `h_adj_at_bad : ¬ Coprime p N → HasBadPrimeFrickePetNAdjoint`
makes T170 only required where it applies (bad primes). The result reaches the
classical `cuspFormsNew`, sufficient for downstream SMO consumers operating
at the classical newspace level. The strengthened input hypothesis `f ∈
cuspFormsNewExtended` (rather than `f ∈ cuspFormsNew`) is what enables the
bad-prime case via T174/T177/T178. -/
theorem heckeT_n_cusp_preserves_cuspFormsNew_of_NewformExtended_of_T170_unified
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p] (hp : p.Prime)
    (h_adj_at_bad : ¬ Nat.Coprime p N → Newform.HasBadPrimeFrickePetNAdjoint N k p)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hf : f ∈ cuspFormsNewExtended N k) :
    heckeT_n_cusp k p f ∈ cuspFormsNew N k := by
  by_cases hpN : Nat.Coprime p N
  · -- Coprime case: f ∈ cuspFormsNew via inclusion; classical preservation.
    exact heckeT_n_preserves_cuspFormsNew p hpN f
      (cuspFormsNewExtended_le_cuspFormsNew hf)
  · -- Bad-prime case: T178 endpoint with T170 hypothesis.
    exact heckeT_n_cusp_preserves_cuspFormsNew_of_NewformExtended_at_divN_of_T170
      hp hpN (h_adj_at_bad hpN) f hf

/-- **T179 NewformExtended-level convenience**: bundled `NewformExtended` form
of the unified Hecke consumer. -/
theorem NewformExtended.heckeT_n_cusp_mem_cuspFormsNew_of_T170
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p] (hp : p.Prime)
    (h_adj_at_bad : ¬ Nat.Coprime p N → Newform.HasBadPrimeFrickePetNAdjoint N k p)
    (f : NewformExtended N k) :
    heckeT_n_cusp k p f.toCuspForm ∈ cuspFormsNew N k :=
  heckeT_n_cusp_preserves_cuspFormsNew_of_NewformExtended_of_T170_unified
    hp h_adj_at_bad f.toCuspForm f.isNew

/-- **T179: For `(p, N) = 1`, every `NewformExtended` is preserved (cuspFormsNew)
without any T170 hypothesis.**

Pure-classical case extracted as a clean unconditional consumer (no T170
needed for coprime primes). -/
theorem NewformExtended.heckeT_n_cusp_mem_cuspFormsNew_of_coprime
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p]
    (hp_cop : Nat.Coprime p N) (f : NewformExtended N k) :
    heckeT_n_cusp k p f.toCuspForm ∈ cuspFormsNew N k :=
  heckeT_n_preserves_cuspFormsNew p hp_cop f.toCuspForm
    (cuspFormsNewExtended_le_cuspFormsNew f.isNew)

/-- **T179 dependency audit (post-T177)**: namespace-level documentation of
the SMO downstream dependency state.

After T177 (`HasHeckeT_n_cusp_at_divN_PreservesCuspFormsOldExtended_unconditional`)
and T173 (`hasFrickeSlashCuspFormPreservesCuspFormsOldExtended`), the
unconditional bad-prime newspace preservation reduces to the **single live
dependency** `Newform.HasBadPrimeFrickePetNAdjoint N k p` (T170 territory).

The streamlined consumer chain is:
1. `Newform.heckeT_n_cusp_preserves_cuspFormsNewExtended_at_divN_of_T170` (T178)
   — bad-prime extended-newspace preservation, T170 only.
2. `heckeT_n_cusp_preserves_cuspFormsNew_of_NewformExtended_at_divN_of_T170` (T178)
   — bad-prime classical-newspace consumer.
3. `heckeT_n_cusp_preserves_cuspFormsNew_of_NewformExtended_of_T170_unified` (T179)
   — unified all-prime Hecke consumer combining classical coprime with T178/T170.
4. `NewformExtended.heckeT_n_cusp_mem_cuspFormsNew_of_T170` (T179) — bundled
   `NewformExtended`-level all-prime Hecke consumer.

Once T170 is discharged unconditionally (a future
`Newform.hasBadPrimeFrickePetNAdjoint N k p` theorem), all four become
unconditional and SMO downstream consumers can iterate Hecke on
`NewformExtended` forms without conditional hypotheses.

This is **not** a theorem with mathematical content — it is a `True`-valued
declaration whose proof type-checks the named theorems above for accessibility. -/
theorem T179_dependency_audit_after_T177 : True := by
  let _ := @Newform.HasBadPrimeFrickePetNAdjoint
  let _ := @Newform.HasHeckeT_n_cusp_at_divN_PreservesCuspFormsOldExtended_unconditional
  let _ := @Newform.hasFrickeSlashCuspFormPreservesCuspFormsOldExtended
  let _ := @Newform.heckeT_n_cusp_preserves_cuspFormsNewExtended_at_divN_of_T170
  let _ := @heckeT_n_cusp_preserves_cuspFormsNew_of_NewformExtended_at_divN_of_T170
  let _ := @heckeT_n_cusp_preserves_cuspFormsNew_of_NewformExtended_of_T170_unified
  let _ := @NewformExtended.heckeT_n_cusp_mem_cuspFormsNew_of_T170
  let _ := @NewformExtended.heckeT_n_cusp_mem_cuspFormsNew_of_coprime
  let _ := @Newform.frickeBadAdjointCandidate_preserves_cuspFormsOldExtended_unconditional
  let _ := @Newform.frickeBadAdjointCandidateNormalized_preserves_cuspFormsOldExtended_unconditional
  trivial

/-! ### T180: Arbitrary-`n` Hecke stability for `NewformExtended`

Building on the T179 prime-level unified consumer, this section extends the
`NewformExtended` Hecke stability statement to arbitrary `n : ℕ`. The current
Hecke API supports the following routes:

* **Coprime `(n, N) = 1`**: classical `heckeT_n_preserves_cuspFormsNew` gives
  unconditional preservation; combined with `cuspFormsNewExtended ⊆ cuspFormsNew`
  this yields a clean delegation theorem (no T170 needed).
* **Prime power `p^v` for bad `p ∣ N`**: by `heckeT_ppow_eq_pow_of_not_coprime`,
  `T_{p^v} = (T_p)^v` at the operator level; iterating T178's bad-prime
  preservation gives `T_{p^v}` preservation of `cuspFormsNewExtended`.
* **Bad-only arbitrary `n`** (all prime factors of `n` divide `N`): strong
  induction over the prime factorization, peeling off `T_{p^v}` for each
  bad prime power and applying the iterated T178 preservation.

The fully-general arbitrary-`n` consumer requires combining the bad-only
stability with the coprime classical preservation via the multiplicative
factorization `n = n_bad · n_cop` with `(n_bad, n_cop) = 1`; this section
provides the components required for that final step. -/

/-- **T180 — coprime arbitrary-`n` consumer for `NewformExtended`.**

Trivial delegation: `NewformExtended` lives in `cuspFormsNewExtended ⊆ cuspFormsNew`,
and classical `heckeT_n_preserves_cuspFormsNew` handles arbitrary `n` coprime to `N`.

No T170 hypothesis needed; this is the unconditional coprime consumer. -/
theorem NewformExtended.heckeT_n_cusp_mem_cuspFormsNew_of_coprime_arbitrary_n
    {N : ℕ} [NeZero N] {k : ℤ} {n : ℕ} [NeZero n] (hn : Nat.Coprime n N)
    (f : NewformExtended N k) :
    heckeT_n_cusp k n f.toCuspForm ∈ cuspFormsNew N k :=
  heckeT_n_preserves_cuspFormsNew n hn f.toCuspForm
    (cuspFormsNewExtended_le_cuspFormsNew f.isNew)

/-- **T180 helper — operator-level decomposition `T_{p^(v+1)} = T_p · T_{p^v}` at
bad primes.**

For a bad prime `p ∣ N`, the diamond term in the Hecke recursion vanishes
(`heckeT_ppow_eq_pow_of_not_coprime`), so `T_{p^v} = (T_p)^v` at the operator
level. This lemma packages the operator equation needed for the iteration. -/
private lemma heckeT_n_succ_pp_eq_at_bad_prime
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p] (hp : p.Prime)
    (hpN : ¬ Nat.Coprime p N) (v : ℕ) :
    haveI : NeZero (p ^ v) := ⟨pow_ne_zero _ hp.ne_zero⟩
    haveI : NeZero (p ^ (v + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
    heckeT_n (N := N) k (p ^ (v + 1)) =
      heckeT_n k p * heckeT_n k (p ^ v) := by
  haveI : NeZero (p ^ v) := ⟨pow_ne_zero _ hp.ne_zero⟩
  haveI : NeZero (p ^ (v + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rcases Nat.eq_zero_or_pos v with hv0 | hv_pos
  · -- v = 0: p^(0+1) = p^1 = p (defeq via pow). Use heckeT_n_prime_pow + heckeT_ppow_one.
    subst hv0
    have h1 : heckeT_n (N := N) k (p ^ 1) = heckeT_n k p := by
      haveI : NeZero (p ^ 1) := ⟨pow_ne_zero _ hp.ne_zero⟩
      rw [heckeT_n_prime_pow k hp 1 Nat.one_pos, heckeT_ppow_one, heckeT_n_prime k hp]
    have h2 : heckeT_n (N := N) k (p ^ 0) = 1 := heckeT_n_one k
    rw [h1, h2, mul_one]
  · -- v ≥ 1: use heckeT_n_prime_pow + heckeT_ppow_eq_pow_of_not_coprime + pow_succ'.
    rw [heckeT_n_prime_pow k hp (v + 1) (Nat.succ_pos v),
      heckeT_n_prime k hp,
      heckeT_n_prime_pow k hp v hv_pos,
      heckeT_ppow_eq_pow_of_not_coprime k hp hpN (v + 1),
      heckeT_ppow_eq_pow_of_not_coprime k hp hpN v,
      pow_succ' (heckeT_p_all k p hp) v]

/-- **T180 — Hecke `T_{p^v}` preservation of `cuspFormsNewExtended` at bad primes.**

For a bad prime `p ∣ N` with the T170 hypothesis `HasBadPrimeFrickePetNAdjoint`
discharged, `T_{p^v}` preserves `cuspFormsNewExtended` for every `v : ℕ`.

Proof: induction on `v`.
* `v = 0`: `T_{p^0} = T_1 = id`, preservation is trivial.
* `v + 1`: `T_{p^(v+1)} = T_p · T_{p^v}` at the operator level (via the bad-prime
  diamond-vanishing recursion), so at the function level
  `T_{p^(v+1)} f = T_p (T_{p^v} f)`. Apply the IH to get `T_{p^v} f ∈
  cuspFormsNewExtended`, then T178's prime-level bad-prime preservation. -/
theorem NewformExtended.heckeT_pp_cusp_mem_cuspFormsNewExtended_at_bad_of_T170
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p] (hp : p.Prime)
    (hpN : ¬ Nat.Coprime p N)
    (h_adj : Newform.HasBadPrimeFrickePetNAdjoint N k p)
    (v : ℕ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hf : f ∈ cuspFormsNewExtended N k) :
    haveI : NeZero (p ^ v) := ⟨pow_ne_zero _ hp.ne_zero⟩
    heckeT_n_cusp k (p ^ v) f ∈ cuspFormsNewExtended N k := by
  induction v with
  | zero =>
    haveI : NeZero (p ^ 0) := ⟨by simp⟩
    -- T_{p^0} = T_1 = id, applied to f gives f.
    have h_op : heckeT_n (N := N) k (p ^ 0) = 1 := heckeT_n_one k
    have h_eq : heckeT_n_cusp k (p ^ 0) f = f := by
      apply CuspForm.ext; intro z
      show (heckeT_n k (p ^ 0) f.toModularForm').toFun z = f z
      rw [h_op]; rfl
    rw [h_eq]; exact hf
  | succ v ih =>
    haveI : NeZero (p ^ v) := ⟨pow_ne_zero _ hp.ne_zero⟩
    haveI : NeZero (p ^ (v + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
    -- Function-level decomposition: T_{p^(v+1)} f = T_p (T_{p^v} f), via the
    -- operator equation `heckeT_n_succ_pp_eq_at_bad_prime`.
    have h_step : heckeT_n_cusp k (p ^ (v + 1)) f =
        heckeT_n_cusp k p (heckeT_n_cusp k (p ^ v) f) := by
      apply CuspForm.ext; intro z
      show (heckeT_n k (p ^ (v + 1)) f.toModularForm').toFun z =
        ((heckeT_n k p) ((heckeT_n k (p ^ v)) f.toModularForm')).toFun z
      rw [heckeT_n_succ_pp_eq_at_bad_prime hp hpN v]; rfl
    rw [h_step]
    -- T_{p^v} f ∈ cuspFormsNewExtended (IH); T_p applied at bad p preserves it (T178).
    exact Newform.heckeT_n_cusp_preserves_cuspFormsNewExtended_at_divN_of_T170
      hp hpN h_adj _ ih

/-- **T180 — bad-only arbitrary-`n` consumer for `cuspFormsNewExtended`.**

For `n : ℕ` whose every prime factor divides `N` (i.e., `n` is supported on
bad primes), with T170 hypotheses discharged for each such prime, `T_n`
preserves `cuspFormsNewExtended`.

Proof: strong induction on `n`. Peel off the smallest prime factor's
prime-power contribution via `heckeT_n_unfold`; apply the bad prime power
preservation theorem (T180) for the peeled-off piece, then recurse on the
quotient (which inherits the bad-only property since divisors of `n` keep
their prime factors among `n`'s primes). -/
theorem NewformExtended.heckeT_n_cusp_mem_cuspFormsNewExtended_of_bad_only_T170
    {N : ℕ} [NeZero N] {k : ℤ} (n : ℕ) [NeZero n]
    (h_bad_only : ∀ p, p.Prime → p ∣ n → ¬ Nat.Coprime p N)
    (h_adj_at_each : ∀ (p : ℕ) [NeZero p], p.Prime → p ∣ n →
      Newform.HasBadPrimeFrickePetNAdjoint N k p)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hf : f ∈ cuspFormsNewExtended N k) :
    heckeT_n_cusp k n f ∈ cuspFormsNewExtended N k := by
  -- Strengthen IH to be over all forms in cuspFormsNewExtended.
  suffices h : ∀ (m : ℕ) (_ : 0 < m),
      (∀ p, p.Prime → p ∣ m → ¬ Nat.Coprime p N) →
      (∀ (p : ℕ) [NeZero p], p.Prime → p ∣ m →
          Newform.HasBadPrimeFrickePetNAdjoint N k p) →
      ∀ (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
        g ∈ cuspFormsNewExtended N k →
        haveI : NeZero m := ⟨by omega⟩
        heckeT_n_cusp k m g ∈ cuspFormsNewExtended N k from
    h n (NeZero.pos n) h_bad_only h_adj_at_each f hf
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm_pos h_bad h_adj g hg
    haveI : NeZero m := ⟨by omega⟩
    by_cases hm1 : m = 1
    · subst hm1
      have h_eq : heckeT_n_cusp k 1 g = g := by
        apply CuspForm.ext; intro z
        show (heckeT_n k 1 g.toModularForm').toFun z = g z
        rw [heckeT_n_one]; rfl
      rw [h_eq]; exact hg
    · have hm_gt : 1 < m := by omega
      set p := m.minFac with hp_def
      have hpp : p.Prime := Nat.minFac_prime (by omega : m ≠ 1)
      set v := m.factorization p with hv_def
      have hv_pos : 0 < v :=
        hpp.factorization_pos_of_dvd (by omega) (Nat.minFac_dvd m)
      have hpv_pos : 0 < p ^ v := pow_pos hpp.pos v
      have hdiv_pos : 0 < m / p ^ v :=
        Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.ordProj_dvd m p)) hpv_pos
      have hdiv_lt : m / p ^ v < m := heckeT_n_unfold_lt m hm_gt
      haveI : NeZero (p ^ v) := ⟨hpv_pos.ne'⟩
      haveI : NeZero (m / p ^ v) := ⟨hdiv_pos.ne'⟩
      haveI : NeZero p := ⟨hpp.ne_zero⟩
      -- p is bad (since p ∣ m, and m is bad-only).
      have hpN : ¬ Nat.Coprime p N := h_bad p hpp (Nat.minFac_dvd m)
      have h_adj_p : Newform.HasBadPrimeFrickePetNAdjoint N k p :=
        h_adj p hpp (Nat.minFac_dvd m)
      -- Function-level decomposition via heckeT_n_cusp_unfold.
      have h_decomp : heckeT_n_cusp k m g =
          heckeT_n_cusp k (p ^ v) (heckeT_n_cusp k (m / p ^ v) g) := by
        apply CuspForm.ext; intro z
        exact heckeT_n_cusp_unfold m hm_gt g z
      rw [h_decomp]
      -- IH: T_{m/p^v} g ∈ cuspFormsNewExtended (m/p^v < m, divisors of m/p^v ⊆ divisors of m).
      have h_mid : heckeT_n_cusp k (m / p ^ v) g ∈ cuspFormsNewExtended N k :=
        ih (m / p ^ v) hdiv_lt hdiv_pos
          (fun q hq hqdiv =>
            h_bad q hq (hqdiv.trans (Nat.div_dvd_of_dvd (Nat.ordProj_dvd m p))))
          (fun q _hq_NeZ hq_prime hqdiv =>
            h_adj q hq_prime (hqdiv.trans (Nat.div_dvd_of_dvd (Nat.ordProj_dvd m p))))
          g hg
      -- Apply T_{p^v} preservation at bad prime p.
      exact NewformExtended.heckeT_pp_cusp_mem_cuspFormsNewExtended_at_bad_of_T170
        hpp hpN h_adj_p v _ h_mid

/-- **T180 — bad-only arbitrary-`n` `NewformExtended` consumer.**

Bundled `NewformExtended`-level wrapper of the bad-only arbitrary-`n` consumer. -/
theorem NewformExtended.heckeT_n_cusp_mem_cuspFormsNew_of_bad_only_T170
    {N : ℕ} [NeZero N] {k : ℤ} {n : ℕ} [NeZero n]
    (h_bad_only : ∀ p, p.Prime → p ∣ n → ¬ Nat.Coprime p N)
    (h_adj_at_each : ∀ (p : ℕ) [NeZero p], p.Prime → p ∣ n →
      Newform.HasBadPrimeFrickePetNAdjoint N k p)
    (f : NewformExtended N k) :
    heckeT_n_cusp k n f.toCuspForm ∈ cuspFormsNew N k :=
  cuspFormsNewExtended_le_cuspFormsNew
    (NewformExtended.heckeT_n_cusp_mem_cuspFormsNewExtended_of_bad_only_T170
      n h_bad_only h_adj_at_each f.toCuspForm f.isNew)

/-- **T180 dependency audit (post-T179)**: refined dependency state for SMO route.

After T179 (unified prime-level consumer) and T180 (bad-only arbitrary-`n`,
coprime arbitrary-`n`, bad-prime-power consumers), the remaining gap to a fully
unconditional arbitrary-`n` Hecke stability theorem for `NewformExtended` is:

1. **Combining bad and coprime parts** for mixed-`n`: requires factorizing
   `n = n_bad · n_cop` with `Nat.Coprime n_bad n_cop` and applying
   `heckeT_n_mul_coprime` plus the existing bad-only and coprime arbitrary-`n`
   consumers. This is a Nat-factorization manipulation, not a deep theorem.
2. **T170 itself**: `Newform.HasBadPrimeFrickePetNAdjoint N k p` (Secondary's
   territory); once unconditional, all T180 hypotheses about T170 vanish.

This is **not** a theorem with mathematical content — it is a `True`-valued
declaration whose proof type-checks the named theorems above for accessibility
and records the post-T180 dependency state. -/
theorem T180_dependency_audit_after_T179 : True := by
  let _ := @NewformExtended.heckeT_n_cusp_mem_cuspFormsNew_of_coprime_arbitrary_n
  let _ := @NewformExtended.heckeT_pp_cusp_mem_cuspFormsNewExtended_at_bad_of_T170
  let _ := @NewformExtended.heckeT_n_cusp_mem_cuspFormsNewExtended_of_bad_only_T170
  let _ := @NewformExtended.heckeT_n_cusp_mem_cuspFormsNew_of_bad_only_T170
  let _ := @heckeT_n_mul_coprime
  trivial

/-- **Matrix-level Fricke / bad-prime upper coset double-conjugation
identity (T149 main matrix helper).**

For the bad-prime upper-triangular coset rep `β_b := T_p_upper p hp b` (matrix
`!![1, b; 0, p]` in `GL (Fin 2) ℚ`), embedded into `GL (Fin 2) ℝ` via `glMap`,
the double-conjugation `W_N · β_b · W_N` (with `W_N` *twice*, no inverse) is
the scalar matrix `(-N) • !![p, 0; -N·b, 1]` at the matrix level.

Direct matrix computation:
```
W_N · β_b = !![0, -1; N, 0] · !![1, b; 0, p] = !![0, -p; N, N·b].
W_N · β_b · W_N = !![0, -p; N, N·b] · !![0, -1; N, 0]
              = !![-N·p, 0; N²·b, -N]
              = (-N) • !![p, 0; -N·b, 1].
```
The factor `(-N)` is exactly the underlying scalar of `W_N · W_N` from T141
(`Newform.frickeMatrix_mul_self_val`); after dividing by it (i.e. using the
INVERSE-conjugation `W_N · β_b · W_N⁻¹`), the scalar cancels — see the
companion lemma `Newform.frickeMatrix_mul_glMap_T_p_upper_mul_frickeMatrix_inv_val`. -/
lemma Newform.frickeMatrix_mul_glMap_T_p_upper_mul_frickeMatrix_val
    (N : ℕ) [NeZero N] {p : ℕ} (hp : 0 < p) (b : ℕ) :
    ((Newform.frickeMatrix N : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) *
        ((glMap (T_p_upper p hp b) : GL (Fin 2) ℝ) :
          Matrix (Fin 2) (Fin 2) ℝ) *
        ((Newform.frickeMatrix N : GL (Fin 2) ℝ) :
          Matrix (Fin 2) (Fin 2) ℝ) =
      (-(N : ℝ)) •
        (!![(p : ℝ), 0; -((N : ℝ) * b), 1] : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [Newform.frickeMatrix_coe]
  rw [show ((glMap (T_p_upper p hp b) : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) =
      !![(1 : ℝ), (b : ℝ); 0, (p : ℝ)] by
    show (T_p_upper p hp b : Matrix (Fin 2) (Fin 2) ℚ).map (algebraMap ℚ ℝ) =
        !![(1 : ℝ), (b : ℝ); 0, (p : ℝ)]
    rw [T_p_upper_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply]]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val',
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply] <;>
    ring

/-- **Matrix-level Fricke / bad-prime upper coset INVERSE-conjugation
identity (T149 inverse-conjugation main matrix helper).**

For the bad-prime upper-triangular coset rep `β_b := T_p_upper p hp b`
(matrix `!![1, b; 0, p]`), embedded into `GL (Fin 2) ℝ` via `glMap`, the
classical Atkin-Lehner inverse-conjugation `W_N · β_b · W_N⁻¹` equals
`!![p, 0; -N·b, 1]` at the matrix level (no scalar — the `(-N)` factor from
the double-conjugation `W_N · β_b · W_N` cancels against `W_N⁻¹ = -1/N · W_N`
that comes from `W_N² = -N • 1`).

Proof: combine the double-conjugation identity
`Newform.frickeMatrix_mul_glMap_T_p_upper_mul_frickeMatrix_val` with
`Matrix.coe_units_inv` to convert between the GL inverse and the matrix
inverse, and `Newform.frickeMatrix_mul_self_val` for the `W_N²` scalar
identity. -/
lemma Newform.frickeMatrix_mul_glMap_T_p_upper_mul_frickeMatrix_inv_val
    (N : ℕ) [NeZero N] {p : ℕ} (hp : 0 < p) (b : ℕ) :
    ((Newform.frickeMatrix N : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) *
        ((glMap (T_p_upper p hp b) : GL (Fin 2) ℝ) :
          Matrix (Fin 2) (Fin 2) ℝ) *
        (((Newform.frickeMatrix N)⁻¹ : GL (Fin 2) ℝ) :
          Matrix (Fin 2) (Fin 2) ℝ) =
      (!![(p : ℝ), 0; -((N : ℝ) * b), 1] : Matrix (Fin 2) (Fin 2) ℝ) := by
  -- Strategy: multiply both sides of the doubled identity on the right by
  -- (W_N²)⁻¹ = -1/N • 1, using W_N · W_N⁻¹ = 1.
  have h_double := Newform.frickeMatrix_mul_glMap_T_p_upper_mul_frickeMatrix_val N hp b
  -- (A * β * W_N) * W_N⁻¹ = A * β * (W_N * W_N⁻¹) = A * β * 1 = A * β.
  -- But that's NOT what we want — we want A * β * W_N⁻¹, which equals
  -- (A * β * W_N) * W_N⁻¹ * W_N⁻¹⁻¹ = (A * β * W_N) * W_N⁻¹ = ...
  -- Actually direct: (W_N · β_b · W_N⁻¹) = (W_N · β_b · W_N) · W_N⁻²
  --                                       = (-N • !![p,0;-Nb,1]) · ((-N)⁻¹ • 1)
  --                                       = !![p,0;-Nb,1].
  have hN_ne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hN_neg_ne : -(N : ℝ) ≠ 0 := neg_ne_zero.mpr hN_ne
  -- W_N⁻¹.val = (W_N.val)⁻¹ via Matrix.coe_units_inv.
  have h_inv : (((Newform.frickeMatrix N)⁻¹ : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) =
      ((Newform.frickeMatrix N : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ)⁻¹ :=
    Matrix.coe_units_inv (Newform.frickeMatrix N)
  rw [h_inv]
  -- Goal: A * β * W_N⁻¹ = M (where M is the target matrix).
  -- Multiply both sides by W_N on the right: A * β * W_N⁻¹ * W_N = A * β,
  -- so A * β = M * W_N. We can then use h_double + cancellation.
  -- Equivalently, show A * β = (M : Matrix) * W_N.val using both sides.
  have hW_inv_mul : ((Newform.frickeMatrix N : GL (Fin 2) ℝ) :
          Matrix (Fin 2) (Fin 2) ℝ) *
        ((Newform.frickeMatrix N : GL (Fin 2) ℝ) :
          Matrix (Fin 2) (Fin 2) ℝ)⁻¹ = 1 := by
    rw [Matrix.mul_nonsing_inv]
    rw [show ((Newform.frickeMatrix N : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ).det = (N : ℝ) from Newform.frickeMatrix_det N]
    exact isUnit_iff_ne_zero.mpr hN_ne
  -- Use: A * β * W_N⁻¹ = (A * β * W_N) * (W_N⁻¹)² ... actually simpler:
  -- LHS' = (A * β) * W_N⁻¹. Use h_double with the FACT that A * β * W_N =
  -- (-N) • M, divide by -N: A * β = (-N)⁻¹ • ((-N) • M * W_N⁻¹) =
  -- This is still convoluted. Let me try yet another approach.
  --
  -- Multiply both sides by W_N on the right:
  --   LHS · W_N = (A * β * W_N⁻¹) * W_N = A * β * (W_N⁻¹ * W_N) = A * β * 1 = A * β
  -- And RHS · W_N = M * W_N
  -- Need: A * β = M * W_N where M = !![p, 0; -Nb, 1].
  -- This is a separate matrix identity; let me verify and prove.
  --
  -- M * W_N = !![p, 0; -Nb, 1] * !![0, -1; N, 0]
  --        = !![p·0 + 0·N, p·(-1)+0·0; -Nb·0+1·N, -Nb·(-1)+1·0]
  --        = !![0, -p; N, Nb] = A * β (computed in docstring).
  -- So A * β = M * W_N. Then A * β * W_N⁻¹ = M * W_N * W_N⁻¹ = M.
  rw [show ((Newform.frickeMatrix N : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) *
        ((glMap (T_p_upper p hp b) : GL (Fin 2) ℝ) :
          Matrix (Fin 2) (Fin 2) ℝ) =
      (!![(p : ℝ), 0; -((N : ℝ) * b), 1] : Matrix (Fin 2) (Fin 2) ℝ) *
        ((Newform.frickeMatrix N : GL (Fin 2) ℝ) :
          Matrix (Fin 2) (Fin 2) ℝ) by
    rw [Newform.frickeMatrix_coe]
    rw [show ((glMap (T_p_upper p hp b) : GL (Fin 2) ℝ) :
          Matrix (Fin 2) (Fin 2) ℝ) =
        !![(1 : ℝ), (b : ℝ); 0, (p : ℝ)] by
      show (T_p_upper p hp b : Matrix (Fin 2) (Fin 2) ℚ).map (algebraMap ℚ ℝ) =
          !![(1 : ℝ), (b : ℝ); 0, (p : ℝ)]
      rw [T_p_upper_coe]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply]]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val',
        Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]]
  rw [Matrix.mul_assoc, hW_inv_mul, Matrix.mul_one]


end HeckeRing.GL2
