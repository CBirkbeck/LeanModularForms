/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GL2.Gamma1Pair

/-!
# Trivial-character eigenspace and `M_k(Γ₀(N))`

The trivial-character Nebentypus eigenspace inside `M_k(Γ₁(N))` is canonically
isomorphic to `M_k(Γ₀(N))`. This file packages the isomorphism

  `modFormCharSpace_one_equiv_Gamma0 :
      modFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ) ≃ₗ[ℂ]
        ModularForm ((Gamma0 N).map (mapGL ℝ)) k`

as a `ℂ`-linear equivalence.

## Mathematical content

* The forward map sends a `Γ₁(N)`-modular form `f` satisfying `⟨d⟩ f = f` for all
  `d ∈ (ZMod N)ˣ` to itself, regarded as a `Γ₀(N)`-modular form. Slash-invariance
  under `Γ₀(N)` follows because every `γ ∈ Γ₀(N)` factors as a diamond representative
  for `d := Gamma0MapUnits γ`, and `diamondOpAux k γ f = f`.
* The backward map sends a `Γ₀(N)`-modular form `g` to itself, regarded as a
  `Γ₁(N)`-modular form (using `Γ₁(N) ≤ Γ₀(N)`). All diamond operators act
  trivially because `g` is `Γ₀(N)`-invariant.

## References

* Diamond–Shurman, *A First Course in Modular Forms*, §5.2 (diamond operators).
* Miyake, *Modular Forms*, §4.5.
-/

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane

open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- A `Γ₁(N)`-form in the trivial-character eigenspace is `Γ₀(N)`-slash-invariant.
The proof factors any `γ ∈ Γ₀(N)` through its diamond operator
`⟨Gamma0MapUnits γ⟩`, which acts as the identity on the trivial-character
eigenspace. -/
private lemma modFormCharSpace_one_slash_Gamma0
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ modFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ))
    {γ : GL (Fin 2) ℝ} (hγ : γ ∈ (Gamma0 N).map (mapGL ℝ)) :
    (⇑f : ℍ → ℂ) ∣[k] γ = ⇑f := by
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hγ
  set g₀ : ↥(Gamma0 N) := ⟨g, hg⟩
  have hd : diamondOp k (Gamma0MapUnits g₀) f = f := by
    simpa using (mem_modFormCharSpace_iff k (1 : (ZMod N)ˣ →* ℂˣ) f).mp hf (Gamma0MapUnits g₀)
  ext z
  exact congrArg (fun h : ModularForm _ _ ↦ h z)
    ((diamondOp_eq_diamondOpAux k (Gamma0MapUnits g₀) g₀ rfl).symm ▸ hd)

/-- The forward map sending an element of the trivial-character eigenspace inside
`M_k(Γ₁(N))` to a `Γ₀(N)`-modular form. -/
noncomputable def modFormCharSpaceOneToGamma0
    (f : modFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ)) :
    ModularForm ((Gamma0 N).map (mapGL ℝ)) k where
  toSlashInvariantForm :=
    { toFun := ⇑(f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
      slash_action_eq' _ hγ :=
        modFormCharSpace_one_slash_Gamma0 f.property hγ }
  holo' := ModularFormClass.holo (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
  bdd_at_cusps' {_} hc :=
    ModularFormClass.bdd_at_cusps (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
      ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mpr
        ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mp hc))

@[simp]
lemma modFormCharSpaceOneToGamma0_apply
    (f : modFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ)) (z : ℍ) :
    modFormCharSpaceOneToGamma0 f z =
      (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) z := rfl

/-- A `Γ₀(N)`-modular form, viewed as a `Γ₁(N)`-modular form via the inclusion
`Γ₁(N) ≤ Γ₀(N)`. -/
noncomputable def modFormGamma0ToGamma1
    (g : ModularForm ((Gamma0 N).map (mapGL ℝ)) k) :
    ModularForm ((Gamma1 N).map (mapGL ℝ)) k where
  toSlashInvariantForm :=
    { toFun := ⇑g
      slash_action_eq' γ hγ :=
        SlashInvariantFormClass.slash_action_eq g γ (Subgroup.map_mono (Gamma1_in_Gamma0 N) hγ) }
  holo' := ModularFormClass.holo g
  bdd_at_cusps' {_} hc :=
    ModularFormClass.bdd_at_cusps g
      ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mpr
        ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mp hc))

@[simp]
lemma modFormGamma0ToGamma1_apply
    (g : ModularForm ((Gamma0 N).map (mapGL ℝ)) k) (z : ℍ) :
    modFormGamma0ToGamma1 g z = g z := rfl

/-- A `Γ₀(N)`-modular form, regarded as a `Γ₁(N)`-form, lies in the trivial-character
eigenspace. Each diamond operator `⟨d⟩` is implemented by some `g ∈ Γ₀(N)`, under
which `g₀` is invariant. -/
lemma modFormGamma0ToGamma1_mem_modFormCharSpace_one
    (g : ModularForm ((Gamma0 N).map (mapGL ℝ)) k) :
    modFormGamma0ToGamma1 g ∈ modFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ) := by
  rw [mem_modFormCharSpace_iff]
  intro d
  obtain ⟨g₀, hg₀⟩ := Gamma0MapUnits_surjective (N := N) d
  have hslash : (⇑g : ℍ → ℂ) ∣[k] mapGL ℝ (g₀ : SL(2, ℤ)) = ⇑g :=
    SlashInvariantFormClass.slash_action_eq g _
      (Subgroup.mem_map.mpr ⟨_, g₀.property, rfl⟩)
  have hd_eq : diamondOp k d (modFormGamma0ToGamma1 g) = modFormGamma0ToGamma1 g := by
    rw [diamondOp_eq_diamondOpAux k d g₀ hg₀]
    exact ModularForm.ext fun _ ↦ congrFun hslash _
  show diamondOp k d (modFormGamma0ToGamma1 g) = _
  rw [hd_eq, show ((1 : (ZMod N)ˣ →* ℂˣ) d : ℂ) = (1 : ℂ) from by simp, one_smul]

/-- The backward map: a `Γ₀(N)`-modular form, regarded as an element of the
trivial-character eigenspace inside `M_k(Γ₁(N))`. -/
noncomputable def modFormGamma0ToCharSpaceOne
    (g : ModularForm ((Gamma0 N).map (mapGL ℝ)) k) :
    modFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ) :=
  ⟨modFormGamma0ToGamma1 g, modFormGamma0ToGamma1_mem_modFormCharSpace_one g⟩

@[simp]
lemma modFormGamma0ToCharSpaceOne_val
    (g : ModularForm ((Gamma0 N).map (mapGL ℝ)) k) :
    (modFormGamma0ToCharSpaceOne g :
        ModularForm ((Gamma1 N).map (mapGL ℝ)) k) = modFormGamma0ToGamma1 g := rfl

/-- The forward map as a `ℂ`-linear map. -/
noncomputable def modFormCharSpaceOneToGamma0Linear :
    modFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ) →ₗ[ℂ]
      ModularForm ((Gamma0 N).map (mapGL ℝ)) k where
  toFun := modFormCharSpaceOneToGamma0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The backward map as a `ℂ`-linear map. -/
noncomputable def modFormGamma0ToCharSpaceOneLinear :
    ModularForm ((Gamma0 N).map (mapGL ℝ)) k →ₗ[ℂ]
      modFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ) where
  toFun := modFormGamma0ToCharSpaceOne
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **The trivial-character eigenspace is `M_k(Γ₀(N))`.** The `ℂ`-linear isomorphism
identifies the diamond-trivial part of `M_k(Γ₁(N))` with `M_k(Γ₀(N))`. -/
noncomputable def modFormCharSpace_one_equiv_Gamma0 (N : ℕ) [NeZero N] (k : ℤ) :
    modFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ) ≃ₗ[ℂ]
      ModularForm ((Gamma0 N).map (mapGL ℝ)) k where
  toFun := modFormCharSpaceOneToGamma0Linear
  map_add' := map_add modFormCharSpaceOneToGamma0Linear
  map_smul' := map_smul modFormCharSpaceOneToGamma0Linear
  invFun := modFormGamma0ToCharSpaceOneLinear
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
lemma modFormCharSpace_one_equiv_Gamma0_apply
    (f : modFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ)) (z : ℍ) :
    modFormCharSpace_one_equiv_Gamma0 N k f z =
      (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) z := rfl

@[simp]
lemma modFormCharSpace_one_equiv_Gamma0_symm_apply
    (g : ModularForm ((Gamma0 N).map (mapGL ℝ)) k) (z : ℍ) :
    ((modFormCharSpace_one_equiv_Gamma0 N k).symm g :
        ModularForm ((Gamma1 N).map (mapGL ℝ)) k) z = g z := rfl

end HeckeRing.GL2
