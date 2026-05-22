-- SPIKE (2026-05-21): feasibility probe for χ-twisted Hecke transport. Not yet wired into the build.
/-
Goal: confirm "step 1" of the planned refactor — bridging the FUNCTION-level
χ-twisted-invariant submodule (`IsGamma0TwistedInvariant`) to the
ModularForm-level nebentypus character space (`modFormCharSpace`).

This is a scratch/exploratory file. It does NOT modify any existing project file.
-/
import LeanModularForms.HeckeRIngs.GL2.Unified.TwistedHeckeRing
import LeanModularForms.HeckeRIngs.GL2.Prop334_HeckeSlashDiag

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup HeckeRing.GLn
open HeckeRing
open scoped Pointwise MatrixGroups ModularForm UpperHalfPlane

namespace HeckeRing.GL2.Unified

open HeckeRing.GL2

variable {N : ℕ} [NeZero N]

/-! ## Target 1: the "forget" direction

`f ∈ modFormCharSpace k χ → IsGamma0TwistedInvariant k χ (⇑f)`.

`modFormCharSpace_iff_nebentypus` gives, for `g : ↥(Gamma0 N)`,
  `f ∣[k] mapGL ℝ (g : SL(2,ℤ)) = χ(Gamma0MapUnits g) • f`.
`IsGamma0TwistedInvariant` requires, for `h ∈ (Gamma0_pair N).H`,
  `f ∣[k] glMap h = (delta0NebentypusHChar χ (GL_adjugate h) _) • f`.

Two gaps:
  (i)  index translation `h = mapGL ℚ (g : SL(2,ℤ))`, `glMap (mapGL ℚ _) = mapGL ℝ _`;
  (ii) CHARACTER convention: `delta0NebentypusHChar χ (GL_adjugate h) _ = χ (Gamma0MapUnits g)`.

Gap (ii) is the reviewer's convention-risk (#7). We isolate it as a bridge lemma.
-/

/-- **Convention bridge lemma (the heart of the convention check).**
For `g ∈ Γ₀(N)`, embedded as `h = mapGL ℚ g ∈ (Gamma0_pair N).H`, the χ-coefficient
used by `IsGamma0TwistedInvariant` (= χ of the upper-left unit of `adj(h)`) equals the
χ-coefficient used by `modFormCharSpace`/`Gamma0MapUnits` (= χ of the lower-right unit
of `g`). Both reduce to `χ` evaluated at the lower-right entry of `g` mod `N`. -/
lemma spike_char_bridge (χ : (ZMod N)ˣ →* ℂˣ) (g : ↥(Gamma0 N))
    (hmem : (mapGL ℚ (g : SL(2, ℤ)) : GL (Fin 2) ℚ) ∈ (Gamma0_pair N).H) :
    delta0NebentypusHChar (N := N) χ (GL_adjugate (mapGL ℚ (g : SL(2, ℤ))))
        (HeckePairAction.adjugate_mem_H _ hmem) =
      χ (Gamma0MapUnits g) := by
  -- Reduce both sides to `χ` of a `(ZMod N)ˣ` unit, then compare underlying values.
  unfold delta0NebentypusHChar delta0NebentypusDeltaChar
  simp only [MonoidHom.coe_mk, OneHom.coe_mk]
  congr 1
  -- Goal: `Delta0UpperUnit ⟨adj (mapGL ℚ g), _⟩ = Gamma0MapUnits g`.
  apply Units.ext
  rw [Delta0UpperUnit_val, Gamma0MapUnits_val]
  -- Goal: `(delta0IntegralMatrix ⟨adj (mapGL ℚ g), _⟩ 0 0 : ZMod N) = Gamma0Map N g`.
  set gZ : Matrix (Fin 2) (Fin 2) ℤ := ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) with hgZ
  -- Abstract the (proof-irrelevant) `.Δ` membership witness of `adj (mapGL ℚ g)`.
  generalize hΔ : (⟨GL_adjugate (mapGL ℚ (g : SL(2, ℤ))), _⟩ : (Gamma0_pair N).Δ) = dEl
  -- Pin down its integer witness as the *integer* adjugate `adjugate gZ`.
  have hval : ((dEl : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
      (gZ.adjugate).map (Int.cast : ℤ → ℚ) := by
    rw [← hΔ]
    show ((GL_adjugate (mapGL ℚ (g : SL(2, ℤ)))).val : Matrix (Fin 2) (Fin 2) ℚ) =
      (gZ.adjugate).map (Int.cast : ℤ → ℚ)
    rw [GL_adjugate_val, mapGL_coe_matrix]
    -- `adjugate (gZ.map (algebraMap ℤ ℚ)) = (adjugate gZ).map Int.cast`.
    have hcomm := (RingHom.map_adjugate (Int.castRingHom ℚ) gZ).symm
    simp only [RingHom.mapMatrix_apply, Int.coe_castRingHom] at hcomm ⊢
    rw [algebraMap_int_eq]
    exact hcomm
  have hwit : delta0IntegralMatrix (N := N) dEl = gZ.adjugate :=
    delta0IntegralMatrix_witness_unique (N := N) dEl _ hval
  rw [hwit, Matrix.adjugate_fin_two]
  -- `(!![gZ 1 1, ...; ...]) 0 0 = gZ 1 1`, and `Gamma0Map N g = (gZ 1 1 : ZMod N)`.
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
    Matrix.cons_val_fin_one]
  rfl

/-- **Target 1.** An element of the diamond χ-eigenspace, viewed as a function, satisfies
the Γ₀(N)-twisted-slash condition. -/
theorem spike_coe_mem_twistedInvariant
    {k : ℤ} {χ : (ZMod N)ˣ →* ℂˣ}
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) (hf : f ∈ modFormCharSpace k χ) :
    IsGamma0TwistedInvariant k χ (⇑f) := by
  -- The function-level nebentypus relation, indexed by `g : ↥(Gamma0 N)`.
  have hneb := (modFormCharSpace_iff_nebentypus k χ f).mp hf
  -- Unfold the target predicate and reduce to the per-element relation.
  intro h hh
  -- `h ∈ (Gamma0_pair N).H = (Gamma0 N).map (mapGL ℚ)`: extract the `SL(2,ℤ)` witness.
  obtain ⟨σ, hσ, hσh⟩ := Subgroup.mem_map.mp hh
  -- Repackage `σ` as an element of `↥(Gamma0 N)`.
  set g : ↥(Gamma0 N) := ⟨σ, hσ⟩ with hg
  -- The function-level relation at `g`.
  have hng := hneb g
  -- `glMap h = mapGL ℝ σ`.
  have hgl : glMap h = (mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (g : SL(2, ℤ)) := by
    rw [← hσh]
    apply Units.ext; ext i j
    simp only [glMap, GeneralLinearGroup.map]
    exact (IsScalarTower.algebraMap_apply ℤ ℚ ℝ ((g : SL(2, ℤ)).1 i j)).symm
  -- LHS: `f ∣[k] glMap h = f ∣[k] mapGL ℝ g = χ(Gamma0MapUnits g) • f`.
  rw [hgl, hng]
  -- RHS coefficient: bridge `delta0NebentypusHChar χ (adj h) _ = χ(Gamma0MapUnits g)`.
  have hmem : (mapGL ℚ (g : SL(2, ℤ)) : GL (Fin 2) ℚ) ∈ (Gamma0_pair N).H :=
    Subgroup.mem_map.mpr ⟨σ, hσ, rfl⟩
  -- We need both the `h`-indexed and `mapGL ℚ g`-indexed forms to match; `h = mapGL ℚ g`.
  have hh_eq : h = mapGL ℚ (g : SL(2, ℤ)) := hσh.symm
  subst hh_eq
  -- Reduce to equality of the χ-coefficients (proof-irrelevance handles the
  -- membership argument inside `delta0NebentypusHChar`).
  congr 1
  rw [← spike_char_bridge (N := N) χ g hmem]

end HeckeRing.GL2.Unified
