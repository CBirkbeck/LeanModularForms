/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GL2.HeckeActionGeneral

/-!
# Hecke algebra acting on `ModularForm ((Gamma0 N).map (mapGL ℝ)) k`

Packages the generalized Hecke action `heckeSlash_gen (Gamma0_pair N)` from
`HeckeActionGeneral.lean` into a ring homomorphism

  `heckeRingHom_Gamma0 N k : 𝕋 (Gamma0_pair N) ℤ →+*
     Module.End ℂ (ModularForm ((Gamma0 N).map (mapGL ℝ)) k)`.

This is the direct analogue of `heckeRingHom` from `HeckeModularForm.lean`,
but at level `Γ₀(N)` instead of `SL₂(ℤ)`. Multiplicativity uses the
commutativity of `𝕋 (Gamma0_pair N) ℤ` (Shimura Prop 3.8, via the
Atkin–Lehner anti-involution, exposed as
`Gamma0_pair_HeckeAlgebra_mul_comm` in `CongruenceHecke.lean`).

## Main definitions

* `heckeOperator_Gamma0 N k D` — `T(D) : ModularForm ((Gamma0 N).map (mapGL ℝ)) k
   → ModularForm ((Gamma0 N).map (mapGL ℝ)) k`
* `heckeOperatorLinear_Gamma0 N k D` — `T(D)` as a ℂ-linear map
* `heckeSum_Gamma0 N k T` — `T = ∑ c_D · [D] ↦ ∑ c_D · T(D)` as a linear map
* `heckeRingHom_Gamma0 N k` — the ring homomorphism `𝕋 (Gamma0_pair N) ℤ
   →+* Module.End ℂ (ModularForm ((Gamma0 N).map (mapGL ℝ)) k)`

## References

* Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §3.4
-/

open Matrix Matrix.SpecialLinearGroup Subgroup.Commensurable Pointwise CongruenceSubgroup
open HeckeRing DoubleCoset HeckeRing.GLn HeckeRing.GL2
open scoped Pointwise ModularForm MatrixGroups UpperHalfPlane Manifold

namespace HeckeRing.GL2

variable (N : ℕ) [NeZero N]

/-! ### Slash–invariance, holomorphicity, and cusp-boundedness transport -/

/-- A `Γ₀(N)`-slash-invariance assumption `∀ γ ∈ (Gamma0 N).map (mapGL ℝ), f ∣[k] γ = f`
converts to the `heckeSlash_gen`-style hypothesis
`∀ h, h ∈ (Gamma0_pair N).H → f ∣[k] glMap h = f`. -/
lemma Gamma0_pair_H_invariant_of_invariant {k : ℤ} {f : ℍ → ℂ}
    (hf : ∀ γ ∈ (Gamma0 N).map (mapGL ℝ), f ∣[k] γ = f)
    (h : GL (Fin 2) ℚ) (hh : h ∈ (Gamma0_pair N).H) :
    f ∣[k] glMap h = f := by
  obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.mp hh
  show f ∣[k] glMap (mapGL ℚ σ) = f
  rw [show glMap (mapGL ℚ σ) = (mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) σ from by
    apply Units.ext; ext i j
    simp only [glMap, GeneralLinearGroup.map]
    exact (IsScalarTower.algebraMap_apply ℤ ℚ ℝ (σ.1 i j)).symm]
  exact hf _ (Subgroup.mem_map.mpr ⟨σ, hσ, rfl⟩)

/-- The Hecke slash action preserves holomorphicity. -/
lemma heckeSlash_gen_Gamma0_holomorphic (k : ℤ) (D : HeckeCoset (Gamma0_pair N))
    (f : ℍ → ℂ) (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (heckeSlash_gen (Gamma0_pair N) k D f) :=
  MDifferentiable.sum fun _ _ => hf.slash k _

/-- `GL₂(ℚ)` maps cusps of `(Gamma0 N).map (mapGL ℝ)` to cusps: the Möbius action
preserves `ℙ¹(ℚ)`, and all arithmetic subgroups share the same cusps. -/
lemma glMap_smul_isCusp_Gamma0 (A : GL (Fin 2) ℚ) {c : OnePoint ℝ}
    (hc : IsCusp c ((Gamma0 N).map (mapGL ℝ))) :
    IsCusp (glMap A • c) ((Gamma0 N).map (mapGL ℝ)) := by
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc ⊢
  rw [isCusp_SL2Z_iff] at hc ⊢
  obtain ⟨q, rfl⟩ := hc
  rw [show glMap A • OnePoint.map (Rat.cast : ℚ → ℝ) q =
      OnePoint.map (Rat.cast : ℚ → ℝ) (A • q)
      from (OnePoint.map_smul (algebraMap ℚ ℝ) A q).symm]
  exact ⟨_, rfl⟩

/-- The Hecke slash action preserves boundedness at cusps. -/
lemma heckeSlash_gen_Gamma0_bdd_at_cusps (k : ℤ) (D : HeckeCoset (Gamma0_pair N))
    (f : ModularForm ((Gamma0 N).map (mapGL ℝ)) k)
    {c : OnePoint ℝ} (hc : IsCusp c ((Gamma0 N).map (mapGL ℝ))) :
    c.IsBoundedAt (heckeSlash_gen (Gamma0_pair N) k D f) k := by
  simp only [heckeSlash_gen]
  apply Finset.sum_induction _ (fun g => c.IsBoundedAt g k) (fun _ _ ha hb => ha.add hb)
    ((0 : ModularForm ((Gamma0 N).map (mapGL ℝ)) k).bdd_at_cusps' hc)
  intro i _
  exact OnePoint.IsBoundedAt.smul_iff.mp (f.bdd_at_cusps' (glMap_smul_isCusp_Gamma0 N _ hc))

/-! ### `heckeOperator_Gamma0`, `heckeOperatorLinear_Gamma0` -/

/-- The `SlashInvariantForm` obtained by applying a Hecke operator at level `Γ₀(N)`. -/
noncomputable def heckeSlashInvariant_Gamma0 (k : ℤ) (D : HeckeCoset (Gamma0_pair N))
    (f : SlashInvariantForm ((Gamma0 N).map (mapGL ℝ)) k) :
    SlashInvariantForm ((Gamma0 N).map (mapGL ℝ)) k where
  toFun := heckeSlash_gen (Gamma0_pair N) k D f
  slash_action_eq' γ hγ := by
    obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.mp hγ
    -- Convert to `h ∈ Gamma0_pair H` using `mapGL ℚ σ` and invoke
    -- `heckeSlash_gen_slash_invariant`.
    have h_inv : ∀ h, h ∈ (Gamma0_pair N).H → (f : ℍ → ℂ) ∣[k] glMap h = f := by
      intro h hh
      exact Gamma0_pair_H_invariant_of_invariant N
        (fun γ' hγ' => f.slash_action_eq' γ' hγ') h hh
    have hmem : (mapGL ℚ σ : GL (Fin 2) ℚ) ∈ (Gamma0_pair N).H :=
      Subgroup.mem_map.mpr ⟨σ, hσ, rfl⟩
    have hgl : glMap (mapGL ℚ σ) = (mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) σ := by
      apply Units.ext; ext i j
      simp only [glMap, GeneralLinearGroup.map]
      exact (IsScalarTower.algebraMap_apply ℤ ℚ ℝ (σ.1 i j)).symm
    have hs := heckeSlash_gen_slash_invariant (P := Gamma0_pair N) k D
      (f : ℍ → ℂ) h_inv (mapGL ℚ σ) hmem
    -- hs : (heckeSlash_gen _ k D ↑f) ∣[k] mapGL ℚ σ = heckeSlash_gen _ k D ↑f
    -- Goal after unfolding: heckeSlash_gen _ k D ↑f ∣[k] mapGL ℝ σ = heckeSlash_gen _ k D ↑f
    change (heckeSlash_gen (Gamma0_pair N) k D (f : ℍ → ℂ)) ∣[k]
        (mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) σ = _
    rw [← hgl]
    exact hs

/-- The Hecke operator `T(D)` on `ModularForm ((Gamma0 N).map (mapGL ℝ)) k`,
preserving slash-invariance, holomorphicity, and boundedness at cusps. -/
noncomputable def heckeOperator_Gamma0 (k : ℤ) (D : HeckeCoset (Gamma0_pair N))
    (f : ModularForm ((Gamma0 N).map (mapGL ℝ)) k) :
    ModularForm ((Gamma0 N).map (mapGL ℝ)) k where
  toSlashInvariantForm := heckeSlashInvariant_Gamma0 N k D f.toSlashInvariantForm
  holo' := heckeSlash_gen_Gamma0_holomorphic N k D f f.holo'
  bdd_at_cusps' hc := heckeSlash_gen_Gamma0_bdd_at_cusps N k D f hc

/-- The Hecke operator `T(D)` as a `ℂ`-linear map on modular forms at level `Γ₀(N)`. -/
noncomputable def heckeOperatorLinear_Gamma0 (k : ℤ) (D : HeckeCoset (Gamma0_pair N)) :
    ModularForm ((Gamma0 N).map (mapGL ℝ)) k →ₗ[ℂ]
      ModularForm ((Gamma0 N).map (mapGL ℝ)) k where
  toFun := heckeOperator_Gamma0 N k D
  map_add' f g := by
    ext z
    change heckeSlash_gen (Gamma0_pair N) k D (↑(f + g)) z =
      (heckeOperator_Gamma0 N k D f + heckeOperator_Gamma0 N k D g) z
    simp only [ModularForm.add_apply]
    change heckeSlash_gen (Gamma0_pair N) k D (↑f + ↑g) z =
      heckeSlash_gen (Gamma0_pair N) k D (↑f) z +
      heckeSlash_gen (Gamma0_pair N) k D (↑g) z
    rw [heckeSlash_gen_add]; rfl
  map_smul' c f := by
    ext z
    change heckeSlash_gen (Gamma0_pair N) k D (↑(c • f)) z =
      (c • heckeOperator_Gamma0 N k D f) z
    change heckeSlash_gen (Gamma0_pair N) k D (c • ↑f) z =
      c • heckeSlash_gen (Gamma0_pair N) k D (↑f) z
    rw [heckeSlash_gen_smul]; rfl

/-! ### Multiplicativity -/

/-- Composition of Hecke operators at level `Γ₀(N)` corresponds to Hecke algebra
multiplication (Shimura Proposition 3.30, generalized). Using commutativity of
`𝕋 (Gamma0_pair N) ℤ` there is no ordering ambiguity. -/
theorem heckeOperator_Gamma0_comp (k : ℤ) (D₁ D₂ : HeckeCoset (Gamma0_pair N))
    (f : ModularForm ((Gamma0 N).map (mapGL ℝ)) k) :
    (heckeOperator_Gamma0 N k D₁ (heckeOperator_Gamma0 N k D₂ f) : ℍ → ℂ) =
    heckeSlashExt_gen (Gamma0_pair N) k
      (T_single (Gamma0_pair N) ℤ D₂ 1 * T_single (Gamma0_pair N) ℤ D₁ 1) f := by
  apply heckeSlash_gen_comp (P := Gamma0_pair N) k D₁ D₂ (f : ℍ → ℂ)
    (fun h hh => Gamma0_pair_H_invariant_of_invariant N
      (fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ) h hh)
  exact Gamma0_pair_HeckeAlgebra_mul_comm N _ _

/-! ### `heckeSum_Gamma0` -/

/-- The `ℂ`-linear endomorphism of `ModularForm ((Gamma0 N).map (mapGL ℝ)) k`
attached to a Hecke algebra element `T : 𝕋 (Gamma0_pair N) ℤ`, obtained by
extending `heckeOperatorLinear_Gamma0` by `ℤ`-linearity. -/
noncomputable def heckeSum_Gamma0 (k : ℤ) (T : 𝕋 (Gamma0_pair N) ℤ) :
    Module.End ℂ (ModularForm ((Gamma0 N).map (mapGL ℝ)) k) :=
  T.sum (fun D c => c • heckeOperatorLinear_Gamma0 N k D)

@[simp] lemma heckeSum_Gamma0_zero (k : ℤ) :
    heckeSum_Gamma0 N k (0 : 𝕋 (Gamma0_pair N) ℤ) = 0 :=
  Finsupp.sum_zero_index

@[simp] lemma heckeSum_Gamma0_T_single (k : ℤ) (D : HeckeCoset (Gamma0_pair N)) (c : ℤ) :
    heckeSum_Gamma0 N k (T_single (Gamma0_pair N) ℤ D c) =
      c • heckeOperatorLinear_Gamma0 N k D :=
  Finsupp.sum_single_index (by simp)

lemma heckeSum_Gamma0_add (k : ℤ) (T₁ T₂ : 𝕋 (Gamma0_pair N) ℤ) :
    heckeSum_Gamma0 N k (T₁ + T₂) =
      heckeSum_Gamma0 N k T₁ + heckeSum_Gamma0 N k T₂ :=
  Finsupp.sum_add_index' (h_zero := fun _ => by simp)
    (h_add := fun _ c₁ c₂ => by rw [add_zsmul])

/-- Pointwise agreement of `heckeSum_Gamma0 N k T f` and the underlying
generalized slash sum `heckeSlashExt_gen (Gamma0_pair N) k T f`. -/
lemma heckeSum_Gamma0_apply_apply (k : ℤ) (T : 𝕋 (Gamma0_pair N) ℤ)
    (f : ModularForm ((Gamma0 N).map (mapGL ℝ)) k) (z : ℍ) :
    (heckeSum_Gamma0 N k T f) z =
      heckeSlashExt_gen (Gamma0_pair N) k T (f : ℍ → ℂ) z := by
  classical
  induction T using Finsupp.induction_linear with
  | zero =>
    simp only [heckeSum_Gamma0_zero, LinearMap.zero_apply, ModularForm.zero_apply]
    unfold heckeSlashExt_gen
    rw [Finsupp.sum_zero_index]; rfl
  | add T₁ T₂ h₁ h₂ =>
    rw [heckeSum_Gamma0_add]
    simp only [LinearMap.add_apply, ModularForm.add_apply, h₁, h₂]
    unfold heckeSlashExt_gen
    rw [show (T₁ + T₂).sum (fun D c => c • heckeSlash_gen (Gamma0_pair N) k D (f : ℍ → ℂ)) =
        T₁.sum (fun D c => c • heckeSlash_gen (Gamma0_pair N) k D (f : ℍ → ℂ)) +
        T₂.sum (fun D c => c • heckeSlash_gen (Gamma0_pair N) k D (f : ℍ → ℂ)) from
      Finsupp.sum_add_index' (h_zero := fun _ => by simp)
        (h_add := fun _ c₁ c₂ => by rw [add_zsmul])]
    rfl
  | single D c =>
    show (heckeSum_Gamma0 N k (T_single (Gamma0_pair N) ℤ D c) f) z = _
    rw [heckeSum_Gamma0_T_single]
    simp only [LinearMap.smul_apply, ModularForm.smul_apply]
    unfold heckeSlashExt_gen
    rw [Finsupp.sum_single_index (by simp :
      (0 : ℤ) • heckeSlash_gen (Gamma0_pair N) k D _ = _)]
    rfl

/-! ### Hecke algebra identity: `heckeSum_Gamma0 k 1 = 1` -/

/-- Helper: `heckeSlashExt_gen` at `Gamma0_pair N` is `ℤ`-linear in the Hecke-algebra
argument. -/
private lemma heckeSlashExt_gen_Gamma0_zsmul (k : ℤ) (n : ℤ) (T : 𝕋 (Gamma0_pair N) ℤ)
    (f : ℍ → ℂ) :
    heckeSlashExt_gen (Gamma0_pair N) k (n • T) f =
      n • heckeSlashExt_gen (Gamma0_pair N) k T f := by
  unfold heckeSlashExt_gen
  rw [Finsupp.sum_smul_index (g := T) (b := n)
    (h := fun D c => c • heckeSlash_gen (Gamma0_pair N) k D f) (by simp),
    Finsupp.smul_sum]
  refine Finsupp.sum_congr ?_
  intro D _
  exact SemigroupAction.mul_smul _ _ _

/-- `heckeSum_Gamma0` is multiplicative on generators `T_single * T_single`. -/
private lemma heckeSum_Gamma0_mul_T_single (k : ℤ) (D₁ D₂ : HeckeCoset (Gamma0_pair N))
    (a b : ℤ) :
    heckeSum_Gamma0 N k (T_single (Gamma0_pair N) ℤ D₁ a *
        T_single (Gamma0_pair N) ℤ D₂ b) =
      heckeSum_Gamma0 N k (T_single (Gamma0_pair N) ℤ D₁ a) *
        heckeSum_Gamma0 N k (T_single (Gamma0_pair N) ℤ D₂ b) := by
  -- Step 1: flip using commutativity of 𝕋 (Gamma0_pair N) ℤ
  rw [Gamma0_pair_HeckeAlgebra_mul_comm N
    (T_single (Gamma0_pair N) ℤ D₁ a) (T_single (Gamma0_pair N) ℤ D₂ b)]
  apply LinearMap.ext
  intro f
  apply ModularForm.ext
  intro z
  -- Step 2: convert LHS to underlying ℍ → ℂ
  rw [heckeSum_Gamma0_apply_apply]
  -- Step 3: expand T_single * T_single = (b*a) • (T_single 1 * T_single 1)
  have h_prod : T_single (Gamma0_pair N) ℤ D₂ b *
      T_single (Gamma0_pair N) ℤ D₁ a =
      (b * a) • (T_single (Gamma0_pair N) ℤ D₂ 1 *
        T_single (Gamma0_pair N) ℤ D₁ 1) := by
    rw [HeckeRing.T_single_mul_T_single, HeckeRing.T_single_mul_T_single,
      one_smul, one_smul, ← SemigroupAction.mul_smul]
  rw [h_prod, heckeSlashExt_gen_Gamma0_zsmul]
  -- Step 4: apply heckeOperator_Gamma0_comp
  rw [← heckeOperator_Gamma0_comp N k D₁ D₂ f]
  show (b * a : ℤ) • (heckeOperator_Gamma0 N k D₁ (heckeOperator_Gamma0 N k D₂ f) :
        ℍ → ℂ) z =
      ((heckeSum_Gamma0 N k (T_single (Gamma0_pair N) ℤ D₁ a) *
        heckeSum_Gamma0 N k (T_single (Gamma0_pair N) ℤ D₂ b)) f) z
  rw [heckeSum_Gamma0_T_single, heckeSum_Gamma0_T_single]
  show (b * a : ℤ) • (heckeOperator_Gamma0 N k D₁ (heckeOperator_Gamma0 N k D₂ f) :
        ℍ → ℂ) z =
      (a • heckeOperatorLinear_Gamma0 N k D₁)
        ((b • heckeOperatorLinear_Gamma0 N k D₂) f) z
  simp only [LinearMap.smul_apply, ModularForm.smul_apply]
  rw [show (heckeOperatorLinear_Gamma0 N k D₁)
      (b • heckeOperatorLinear_Gamma0 N k D₂ f) =
      b • (heckeOperatorLinear_Gamma0 N k D₁)
        (heckeOperatorLinear_Gamma0 N k D₂ f) from
    (heckeOperatorLinear_Gamma0 N k D₁).map_smul_of_tower b _]
  rw [ModularForm.smul_apply]
  show (b * a : ℤ) • (heckeOperator_Gamma0 N k D₁
          (heckeOperator_Gamma0 N k D₂ f) : ℍ → ℂ) z =
      a • b • (heckeOperator_Gamma0 N k D₁
          (heckeOperator_Gamma0 N k D₂ f) : ℍ → ℂ) z
  rw [smul_smul, mul_comm b a]

lemma heckeSum_Gamma0_mul (k : ℤ) (T₁ T₂ : 𝕋 (Gamma0_pair N) ℤ) :
    heckeSum_Gamma0 N k (T₁ * T₂) =
      heckeSum_Gamma0 N k T₁ * heckeSum_Gamma0 N k T₂ := by
  induction T₁ using Finsupp.induction_linear with
  | zero => simp [zero_mul]
  | add T₁ T₁' h h' =>
    rw [add_mul, heckeSum_Gamma0_add, heckeSum_Gamma0_add, h, h', add_mul]
  | single D₁ a =>
    induction T₂ using Finsupp.induction_linear with
    | zero => simp [mul_zero]
    | add T₂ T₂' h h' =>
      rw [mul_add, heckeSum_Gamma0_add, heckeSum_Gamma0_add, h, h', mul_add]
    | single D₂ b => exact heckeSum_Gamma0_mul_T_single N k D₁ D₂ a b

/-! ### Identity: `heckeSum_Gamma0 N k 1 = 1` -/

/-- The Hecke slash of `HeckeCoset.one` on a `Γ₀(N)`-invariant function equals the
function itself. The single summand in `heckeSlash_gen` is the adjugate of
`q.out · rep(one)`, which lies in `H` (since `H = Γ₀(N).map (mapGL ℚ)` is a
subgroup of `SLnZ_subgroup 2` and adjugate preserves `H`). -/
private lemma heckeSlash_gen_Gamma0_one (k : ℤ) (f : ℍ → ℂ)
    (hf : ∀ h, h ∈ (Gamma0_pair N).H → f ∣[k] glMap h = f) :
    heckeSlash_gen (Gamma0_pair N) k (HeckeCoset.one (Gamma0_pair N)) f = f := by
  haveI : Subsingleton (decompQuot (Gamma0_pair N)
      (HeckeCoset.rep (HeckeCoset.one (Gamma0_pair N)))) :=
    subsingleton_decompQuot_T_one (Gamma0_pair N)
  haveI : Nonempty (decompQuot (Gamma0_pair N)
      (HeckeCoset.rep (HeckeCoset.one (Gamma0_pair N)))) :=
    one_in_decompQuot_T_one (Gamma0_pair N)
  haveI : Unique (decompQuot (Gamma0_pair N)
      (HeckeCoset.rep (HeckeCoset.one (Gamma0_pair N)))) := uniqueOfSubsingleton default
  unfold heckeSlash_gen
  rw [show (Finset.univ : Finset (decompQuot (Gamma0_pair N)
        (HeckeCoset.rep (HeckeCoset.one (Gamma0_pair N))))) = {default} from by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨Finset.mem_univ _, fun i _ => Subsingleton.elim _ _⟩,
    Finset.sum_singleton]
  set q : decompQuot (Gamma0_pair N) (HeckeCoset.rep (HeckeCoset.one (Gamma0_pair N))) :=
    default
  -- The unique element is `tRep_gen ⟦1⟧ = adj(q.out · rep(1))`; since q.out ∈ H and
  -- rep(one) ∈ H, their product is in H, and adj preserves H.
  have hq_mem_H : (q.out : GL (Fin 2) ℚ) ∈ (Gamma0_pair N).H := SetLike.coe_mem _
  have h_rep_mem_H : (HeckeCoset.rep (HeckeCoset.one (Gamma0_pair N)) : GL (Fin 2) ℚ) ∈
      (Gamma0_pair N).H := HeckeCoset.one_rep_mem_H _
  have h_prod_mem : (q.out : GL (Fin 2) ℚ) *
      (HeckeCoset.rep (HeckeCoset.one (Gamma0_pair N)) : GL (Fin 2) ℚ) ∈
      (Gamma0_pair N).H :=
    (Gamma0_pair N).H.mul_mem hq_mem_H h_rep_mem_H
  have h_adj_mem : GL_adjugate
      ((q.out : GL (Fin 2) ℚ) *
        (HeckeCoset.rep (HeckeCoset.one (Gamma0_pair N)) : GL (Fin 2) ℚ)) ∈
      (Gamma0_pair N).H :=
    HeckePairAction.adjugate_mem_H _ h_prod_mem
  show f ∣[k] tRep_gen (Gamma0_pair N) (HeckeCoset.one (Gamma0_pair N)) q = f
  change f ∣[k] glMap (tRep_gen (Gamma0_pair N) (HeckeCoset.one (Gamma0_pair N)) q) = f
  exact hf _ h_adj_mem

/-- `heckeOperator_Gamma0 N k (HeckeCoset.one _) = id`. -/
@[simp] lemma heckeOperator_Gamma0_one (k : ℤ)
    (f : ModularForm ((Gamma0 N).map (mapGL ℝ)) k) :
    heckeOperator_Gamma0 N k (HeckeCoset.one (Gamma0_pair N)) f = f := by
  apply ModularForm.ext
  intro z
  change heckeSlash_gen (Gamma0_pair N) k (HeckeCoset.one (Gamma0_pair N))
      (f : ℍ → ℂ) z = f z
  rw [heckeSlash_gen_Gamma0_one N k (f : ℍ → ℂ)
    (fun h hh => Gamma0_pair_H_invariant_of_invariant N
      (fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ) h hh)]

@[simp] lemma heckeOperatorLinear_Gamma0_one (k : ℤ) :
    heckeOperatorLinear_Gamma0 N k (HeckeCoset.one (Gamma0_pair N)) = 1 := by
  apply LinearMap.ext
  intro f
  show heckeOperator_Gamma0 N k (HeckeCoset.one (Gamma0_pair N)) f = (1 : Module.End ℂ _) f
  rw [Module.End.one_apply, heckeOperator_Gamma0_one]

@[simp] lemma heckeSum_Gamma0_one (k : ℤ) :
    heckeSum_Gamma0 N k (1 : 𝕋 (Gamma0_pair N) ℤ) = 1 := by
  rw [show (1 : 𝕋 (Gamma0_pair N) ℤ) =
      T_single (Gamma0_pair N) ℤ (HeckeCoset.one (Gamma0_pair N)) 1 from
      HeckeRing.one_def _ _,
    heckeSum_Gamma0_T_single, heckeOperatorLinear_Gamma0_one, one_smul]

/-! ### The Hecke ring homomorphism -/

/-- The Hecke algebra `𝕋 (Gamma0_pair N) ℤ` as endomorphisms of
`ModularForm ((Gamma0 N).map (mapGL ℝ)) k` (Shimura Prop 3.30, level `Γ₀(N)`). -/
noncomputable def heckeRingHom_Gamma0 (k : ℤ) :
    𝕋 (Gamma0_pair N) ℤ →+* Module.End ℂ (ModularForm ((Gamma0 N).map (mapGL ℝ)) k) where
  toFun := heckeSum_Gamma0 N k
  map_zero' := heckeSum_Gamma0_zero N k
  map_one' := heckeSum_Gamma0_one N k
  map_add' := heckeSum_Gamma0_add N k
  map_mul' := heckeSum_Gamma0_mul N k

@[simp] lemma heckeRingHom_Gamma0_apply (k : ℤ) (T : 𝕋 (Gamma0_pair N) ℤ) :
    heckeRingHom_Gamma0 N k T = heckeSum_Gamma0 N k T := rfl

@[simp] lemma heckeRingHom_Gamma0_T_single (k : ℤ) (D : HeckeCoset (Gamma0_pair N))
    (c : ℤ) :
    heckeRingHom_Gamma0 N k (T_single (Gamma0_pair N) ℤ D c) =
      c • heckeOperatorLinear_Gamma0 N k D :=
  heckeSum_Gamma0_T_single N k D c

end HeckeRing.GL2
