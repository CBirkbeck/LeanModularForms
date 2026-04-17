/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GL2.Prop334
import LeanModularForms.HeckeRIngs.GL2.HeckeRingHomCharSpace
import LeanModularForms.HeckeRIngs.GL2.HeckeModularForm_Gamma0
import LeanModularForms.HeckeRIngs.GL2.LevelEmbed

/-!
# Prop 3.34 (E) — `heckeSlash_gen` preserves `modFormCharSpace`

This file connects P334-B (`Gamma0MapUnits_preserved_of_detCoprime`) to the
`modFormCharSpace` preservation needed for the full Hecke-ring homomorphism.

## Strategy

For `f ∈ modFormCharSpace k χ` and `D : HeckeCoset (Gamma0_pair N)` with
`CoprimeDet N (rep D)`, we reduce preservation of `modFormCharSpace k χ`
under `heckeSlash_gen (Gamma0_pair N) k D` to a **functional χ-equivariance**
hypothesis:
```
(heckeSlash_gen (Gamma0_pair N) k D ⇑f) ∣[k] mapGL ℝ g =
  (χ (Gamma0MapUnits g) : ℂ) • heckeSlash_gen (Gamma0_pair N) k D ⇑f.
```

This reduction is independent of the proof of the functional equivariance
itself; the latter is the classical Diamond–Shurman Prop 5.2.1 argument
(Hecke operators commute with diamond operators), whose matrix-algebraic
core is P334-B.

## Main results

* `heckeSlash_gen_diamondOpHom_of_functional_comm` — From functional
  χ-equivariance, each diamond operator `⟨d⟩` acts as the scalar `χ d` on
  the Hecke-transformed function.
* `heckeSlash_gen_mem_modFormCharSpace_of_slash_comm` — From functional
  χ-equivariance AND Γ₁(N)-invariance, the transformed form packaged as a
  modular form at the Γ₁(N)-level lies in `modFormCharSpace k χ`.
* `heckeSlash_gen_invariant_Gamma1_of_slash_comm` — Γ₁(N)-invariance of
  the Hecke slash follows from functional χ-equivariance at `d = 1`.

## References

* Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §3.4.
* Diamond–Shurman, *A First Course in Modular Forms*, §5.2, Proposition 5.2.1.
-/

open Matrix Matrix.SpecialLinearGroup HeckeRing.GLn CongruenceSubgroup
open HeckeRing DoubleCoset

open scoped Pointwise MatrixGroups ModularForm UpperHalfPlane Manifold

namespace HeckeRing.GL2

variable {N : ℕ} [NeZero N]

/-! ### Γ₁(N)-invariance from functional χ-equivariance

Any Γ₀(N) element `γ_1 ∈ Γ₁(N)` has `Gamma0MapUnits γ_1 = 1`, so the
χ-twisted slash equivariance at `γ_1` reduces to ordinary invariance. -/

/-- If the χ-equivariance under the slash action by every `g ∈ Γ₀(N)`
holds, then the Hecke-transformed function is Γ₁(N)-invariant. -/
theorem heckeSlash_gen_invariant_Gamma1_of_slash_comm
    (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) (D : HeckeCoset (Gamma0_pair N))
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hComm : ∀ g : ↥(Gamma0 N),
      (heckeSlash_gen (Gamma0_pair N) k D (⇑f : ℍ → ℂ)) ∣[k]
        mapGL ℝ (g : SL(2, ℤ)) =
      (↑(χ (Gamma0MapUnits g)) : ℂ) •
        heckeSlash_gen (Gamma0_pair N) k D (⇑f : ℍ → ℂ))
    (γ : GL (Fin 2) ℝ) (hγ : γ ∈ (Gamma1 N).map (mapGL ℝ)) :
    (heckeSlash_gen (Gamma0_pair N) k D (⇑f : ℍ → ℂ)) ∣[k] γ =
    heckeSlash_gen (Gamma0_pair N) k D (⇑f : ℍ → ℂ) := by
  obtain ⟨σ, hσ_Gamma1, rfl⟩ := Subgroup.mem_map.mp hγ
  have hσ_Gamma0 : σ ∈ Gamma0 N := Gamma1_le_Gamma0 N hσ_Gamma1
  have h_units : Gamma0MapUnits (⟨σ, hσ_Gamma0⟩ : ↥(Gamma0 N)) = 1 := by
    have h := (Gamma1_mem N σ).mp hσ_Gamma1
    ext
    simp only [Gamma0MapUnits_val, Gamma0Map, MonoidHom.coe_mk, OneHom.coe_mk,
      Units.val_one]
    exact h.2.1
  have hc := hComm ⟨σ, hσ_Gamma0⟩
  rw [h_units, map_one, Units.val_one, one_smul] at hc
  exact hc

/-! ### Membership reduction -/

/-- If the functional χ-equivariance of the Hecke slash holds, then for
every `d : (ZMod N)ˣ`, the diamond operator `⟨d⟩` acts on the
Hecke-transformed function as multiplication by `χ d`.

This is the underlying `ℍ → ℂ`-level statement; packaging into a
`ModularForm` plus `modFormCharSpace k χ` membership follows from
`mem_modFormCharSpace_iff`. -/
theorem heckeSlash_gen_diamondOpHom_of_functional_comm
    (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) (D : HeckeCoset (Gamma0_pair N))
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hComm : ∀ g : ↥(Gamma0 N),
      (heckeSlash_gen (Gamma0_pair N) k D (⇑f : ℍ → ℂ)) ∣[k]
        mapGL ℝ (g : SL(2, ℤ)) =
      (↑(χ (Gamma0MapUnits g)) : ℂ) •
        heckeSlash_gen (Gamma0_pair N) k D (⇑f : ℍ → ℂ))
    (d : (ZMod N)ˣ) (g : ↥(Gamma0 N)) (hg : Gamma0MapUnits g = d) :
    (heckeSlash_gen (Gamma0_pair N) k D (⇑f : ℍ → ℂ)) ∣[k]
      mapGL ℝ (g : SL(2, ℤ)) =
    (↑(χ d) : ℂ) •
      heckeSlash_gen (Gamma0_pair N) k D (⇑f : ℍ → ℂ) := by
  rw [hComm g, hg]

/-! ### Packaging as a ModularForm (via Γ₁-invariance + holo + cusps) -/

/-- The Hecke slash preserves holomorphicity. -/
lemma heckeSlash_gen_Gamma1_holomorphic (k : ℤ)
    (D : HeckeCoset (Gamma0_pair N))
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
      (heckeSlash_gen (Gamma0_pair N) k D (⇑f : ℍ → ℂ)) :=
  MDifferentiable.sum fun _ _ => (ModularFormClass.holo f).slash k _

/-- `GL₂(ℚ)` maps cusps of `(Gamma1 N).map (mapGL ℝ)` to cusps. -/
lemma glMap_smul_isCusp_Gamma1 (A : GL (Fin 2) ℚ) {c : OnePoint ℝ}
    (hc : IsCusp c ((Gamma1 N).map (mapGL ℝ))) :
    IsCusp (glMap A • c) ((Gamma1 N).map (mapGL ℝ)) := by
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc ⊢
  rw [isCusp_SL2Z_iff] at hc ⊢
  obtain ⟨q, rfl⟩ := hc
  rw [show glMap A • OnePoint.map (Rat.cast : ℚ → ℝ) q =
      OnePoint.map (Rat.cast : ℚ → ℝ) (A • q)
      from (OnePoint.map_smul (algebraMap ℚ ℝ) A q).symm]
  exact ⟨_, rfl⟩

/-- The Hecke slash preserves boundedness at cusps. -/
lemma heckeSlash_gen_Gamma1_bdd_at_cusps (k : ℤ)
    (D : HeckeCoset (Gamma0_pair N))
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    {c : OnePoint ℝ} (hc : IsCusp c ((Gamma1 N).map (mapGL ℝ))) :
    c.IsBoundedAt (heckeSlash_gen (Gamma0_pair N) k D (⇑f : ℍ → ℂ)) k := by
  simp only [heckeSlash_gen]
  apply Finset.sum_induction _ (fun g => c.IsBoundedAt g k)
    (fun _ _ ha hb => ha.add hb)
    ((0 : ModularForm ((Gamma1 N).map (mapGL ℝ)) k).bdd_at_cusps' hc)
  intro i _
  exact OnePoint.IsBoundedAt.smul_iff.mp
    (f.bdd_at_cusps' (glMap_smul_isCusp_Gamma1 _ hc))

/-! ### The `heckeSlash_gen` action wrapped as a ModularForm -/

/-- Given functional χ-equivariance of `heckeSlash_gen (Gamma0_pair N) k D`
on the underlying function of `f`, package the result as a
`ModularForm ((Gamma1 N).map (mapGL ℝ)) k`. -/
noncomputable def heckeSlash_gen_asModularForm_of_slash_comm
    (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) (D : HeckeCoset (Gamma0_pair N))
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hComm : ∀ g : ↥(Gamma0 N),
      (heckeSlash_gen (Gamma0_pair N) k D (⇑f : ℍ → ℂ)) ∣[k]
        mapGL ℝ (g : SL(2, ℤ)) =
      (↑(χ (Gamma0MapUnits g)) : ℂ) •
        heckeSlash_gen (Gamma0_pair N) k D (⇑f : ℍ → ℂ)) :
    ModularForm ((Gamma1 N).map (mapGL ℝ)) k where
  toFun := heckeSlash_gen (Gamma0_pair N) k D (⇑f : ℍ → ℂ)
  slash_action_eq' γ hγ :=
    heckeSlash_gen_invariant_Gamma1_of_slash_comm k χ D f hComm γ hγ
  holo' := heckeSlash_gen_Gamma1_holomorphic k D f
  bdd_at_cusps' hc := heckeSlash_gen_Gamma1_bdd_at_cusps k D f hc

/-- The underlying function of
`heckeSlash_gen_asModularForm_of_slash_comm` is exactly the
`heckeSlash_gen` sum applied to `⇑f`. -/
@[simp] lemma heckeSlash_gen_asModularForm_of_slash_comm_coe
    (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) (D : HeckeCoset (Gamma0_pair N))
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hComm : ∀ g : ↥(Gamma0 N),
      (heckeSlash_gen (Gamma0_pair N) k D (⇑f : ℍ → ℂ)) ∣[k]
        mapGL ℝ (g : SL(2, ℤ)) =
      (↑(χ (Gamma0MapUnits g)) : ℂ) •
        heckeSlash_gen (Gamma0_pair N) k D (⇑f : ℍ → ℂ)) :
    (⇑(heckeSlash_gen_asModularForm_of_slash_comm k χ D f hComm) :
        ℍ → ℂ) =
      heckeSlash_gen (Gamma0_pair N) k D (⇑f : ℍ → ℂ) := rfl

/-! ### Membership in `modFormCharSpace k χ` -/

/-- The Hecke-transformed modular form lies in `modFormCharSpace k χ`,
given the functional χ-equivariance hypothesis. -/
theorem heckeSlash_gen_mem_modFormCharSpace_of_slash_comm
    (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) (D : HeckeCoset (Gamma0_pair N))
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hComm : ∀ g : ↥(Gamma0 N),
      (heckeSlash_gen (Gamma0_pair N) k D (⇑f : ℍ → ℂ)) ∣[k]
        mapGL ℝ (g : SL(2, ℤ)) =
      (↑(χ (Gamma0MapUnits g)) : ℂ) •
        heckeSlash_gen (Gamma0_pair N) k D (⇑f : ℍ → ℂ)) :
    heckeSlash_gen_asModularForm_of_slash_comm k χ D f hComm ∈
      modFormCharSpace k χ := by
  rw [modFormCharSpace_iff_nebentypus]
  intro g
  show (⇑(heckeSlash_gen_asModularForm_of_slash_comm k χ D f hComm)) ∣[k]
      mapGL ℝ (g : SL(2, ℤ)) =
    (↑(χ (Gamma0MapUnits g)) : ℂ) •
      ⇑(heckeSlash_gen_asModularForm_of_slash_comm k χ D f hComm)
  rw [heckeSlash_gen_asModularForm_of_slash_comm_coe]
  exact hComm g

/-! ### Specialization: trivial character χ = 1

For `χ = 1`, the functional χ-equivariance `hComm` reduces to ordinary
Γ₀(N)-slash invariance, which is precisely `heckeSlash_gen_slash_invariant`
applied to an `H`-invariant function. This gives a direct derivation of
preservation of `modFormCharSpace k 1` without an abstract hypothesis.
The result is a checkpoint confirming the reduction above reproduces the
trivial-character case handled in `HeckeT_p_CharSpace_Comm.lean`. -/

/-- Bridge: an `H`-invariance hypothesis `f ∣[k] glMap h = f` for `h ∈ H`
implies the nebentypus relation against the trivial character for all
`g ∈ Γ₀(N)`. -/
private lemma slash_mapGL_eq_of_H_invariant {k : ℤ}
    (f : ℍ → ℂ)
    (hf : ∀ h, h ∈ (Gamma0_pair N).H → f ∣[k] (glMap h) = f)
    (g : ↥(Gamma0 N)) :
    f ∣[k] mapGL ℝ (g : SL(2, ℤ)) = f := by
  have hmem : (mapGL ℚ (g : SL(2, ℤ)) : GL (Fin 2) ℚ) ∈ (Gamma0_pair N).H :=
    Subgroup.mem_map.mpr ⟨g, g.property, rfl⟩
  have hgl : glMap (mapGL ℚ (g : SL(2, ℤ))) =
      (mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) g := by
    apply Units.ext; ext i j
    simp only [glMap, GeneralLinearGroup.map]
    exact (IsScalarTower.algebraMap_apply ℤ ℚ ℝ ((g : SL(2, ℤ)).val i j)).symm
  have := hf _ hmem
  rw [hgl] at this
  exact this

/-- For the trivial character `χ = 1`, the functional χ-equivariance of
`heckeSlash_gen (Gamma0_pair N) k D` on `⇑f` follows directly from
`heckeSlash_gen_slash_invariant` for any Γ₀(N)-invariant function. -/
theorem heckeSlash_gen_slash_comm_one
    (k : ℤ) (D : HeckeCoset (Gamma0_pair N))
    (f : ℍ → ℂ)
    (hf : ∀ h, h ∈ (Gamma0_pair N).H → f ∣[k] (glMap h) = f)
    (g : ↥(Gamma0 N)) :
    (heckeSlash_gen (Gamma0_pair N) k D f) ∣[k] mapGL ℝ (g : SL(2, ℤ)) =
      (↑((1 : (ZMod N)ˣ →* ℂˣ) (Gamma0MapUnits g)) : ℂ) •
        heckeSlash_gen (Gamma0_pair N) k D f := by
  have hmem : (mapGL ℚ (g : SL(2, ℤ)) : GL (Fin 2) ℚ) ∈ (Gamma0_pair N).H :=
    Subgroup.mem_map.mpr ⟨g, g.property, rfl⟩
  have hgl : glMap (mapGL ℚ (g : SL(2, ℤ))) =
      (mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) g := by
    apply Units.ext; ext i j
    simp only [glMap, GeneralLinearGroup.map]
    exact (IsScalarTower.algebraMap_apply ℤ ℚ ℝ ((g : SL(2, ℤ)).val i j)).symm
  have hinv := heckeSlash_gen_slash_invariant (P := Gamma0_pair N) k D f hf
    (mapGL ℚ (g : SL(2, ℤ))) hmem
  -- hinv : (heckeSlash_gen _ k D f) ∣[k] mapGL ℚ g = heckeSlash_gen _ k D f
  -- Goal: (heckeSlash_gen _ k D f) ∣[k] mapGL ℝ g = 1 • heckeSlash_gen _ k D f
  simp only [MonoidHom.one_apply, Units.val_one, one_smul]
  change (heckeSlash_gen (Gamma0_pair N) k D f) ∣[k]
    (mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) g = _
  rw [← hgl]
  exact hinv

/-! ### Usage

The hypothesis `hComm` of the main results in this file is the
Diamond–Shurman Prop 5.2.1 commutativity `T(D) ⟨d⟩ = ⟨d⟩ T(D)` specialized
to `f ∈ modFormCharSpace k χ` (so that `f ∣[k] γ_d = χ(d) • f`).

The matrix-algebraic engine driving this commutativity is P334-B
(`Gamma0MapUnits_preserved_of_detCoprime`) applied to the K-correction
element arising in `slash_tRep_gen_of_mem`, as sketched in the P334-E
ticket. The coset-bookkeeping portion of the proof is orthogonal to the
content of P334-A/B.

Providing `hComm` from the nebentypus property of `f` and P334-B is the
remaining step. The reduction here shows that once `hComm` is available,
the preservation of `modFormCharSpace k χ` follows cleanly.

For the trivial character `χ = 1`, `heckeSlash_gen_slash_comm_one` above
provides `hComm` directly from `heckeSlash_gen_slash_invariant` — giving
a sanity check that this reduction recovers the χ = 1 case. -/

end HeckeRing.GL2
