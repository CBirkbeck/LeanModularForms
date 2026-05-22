import LeanModularForms.HeckeRIngs.GL2.Unified.TwistedHeckeRing
import LeanModularForms.HeckeRIngs.GL2.Prop334_HeckeSlashDiag
import LeanModularForms.HeckeRIngs.GL2.HeckeT_p_CharSpace_Comm
import LeanModularForms.HeckeRIngs.GL2.MultiplicationTable

/-!
# Nebentypus Hecke ring action

This file constructs the action of the abstract `Γ₀(N)` Hecke ring on a nebentypus
character space and bridges it to the concrete Hecke operators.

## Main definitions

* `heckeRingHomCharSpace` : the general-`χ` ring homomorphism
  `Φ_χ : 𝕋(Γ₀(N)) →+* End_ℂ (Mₖ(Γ₁(N), χ))`, assembling the χ-twisted double-coset
  operators on the nebentypus eigenspace `modFormCharSpace k χ`.  It is built from the
  per-coset twisted Hecke slash `twistedHeckeSlash_gen`, packaged as a `ℂ`-linear
  endomorphism (`nebentypusHeckeOpLinear`) and extended `ℤ`-linearly over the ring
  (`nebentypusHeckeSum`); the ring axioms transport from the proven function-level
  homomorphism `twistedHeckeRingHomFunction` via injectivity of the coercion
  `modFormCharSpace k χ ↪ (ℍ → ℂ)`.

## Main results

* `heckeRingHomCharSpace_D_p_eq_heckeT_p_all` : at a good prime `p ∤ N`, the canonical
  operator at the prime double coset `D_p` is `χ(p)⁻¹` times the concrete operator
  `heckeT_p_all`, identifying the abstract action with the textbook Hecke operator.
* `heckeRingHomCharSpace_T_pp_eq_scalar` : at the scalar coset `T(p,p)` (good prime),
  the action is the scalar `χ(p)⁻¹ · p^(k-2)`.
* `adj_T_p_upper_not_mem_Delta0_of_dvd` : the bad-prime obstruction.  For `p ∣ N` the
  adjugate of the upper-triangular representative escapes `Δ₀(N)`, so the good-prime
  bridge cannot transfer; the discrepancy is the Atkin–Lehner involution.
* `heckeRingHomCharSpace_commute` and `heckeT_p_all_comm_on_charSpace_via_ring` :
  commutativity of the operators on `modFormCharSpace k χ` as a corollary of the
  commutativity of the source ring, with no coset combinatorics.
* `heckeRingHomCharSpace_table_transports_coprime` and
  `heckeRingHomCharSpace_table_transports_ppow_recurrence` : the level-1 multiplication
  identities push forward to operator identities on the χ-space through the Shimura
  surjection `𝕋(GL₂) →+* 𝕋(Γ₀(N))` composed with `heckeRingHomCharSpace`.

## References

* [G. Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*][shimura1971],
  §3.4 (the Hecke ring and its action on modular forms).
* [F. Diamond and J. Shurman, *A First Course in Modular Forms*][diamondshurman2005],
  §5.2 (Hecke operators and the nebentypus / diamond decomposition).
-/

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup HeckeRing.GLn
open HeckeRing
open scoped Pointwise MatrixGroups ModularForm UpperHalfPlane Manifold

namespace HeckeRing.GL2.Unified

open HeckeRing.GL2

variable {N : ℕ} [NeZero N]

/-! ## The "forget" direction

`f ∈ modFormCharSpace k χ → IsGamma0TwistedInvariant k χ (⇑f)`.

`modFormCharSpace_iff_nebentypus` gives, for `g : ↥(Gamma0 N)`,
  `f ∣[k] mapGL ℝ (g : SL(2,ℤ)) = χ(Gamma0MapUnits g) • f`.
`IsGamma0TwistedInvariant` requires, for `h ∈ (Gamma0_pair N).H`,
  `f ∣[k] glMap h = (delta0NebentypusHChar χ (GL_adjugate h) _) • f`.

Two gaps:
  (i)  index translation `h = mapGL ℚ (g : SL(2,ℤ))`, `glMap (mapGL ℚ _) = mapGL ℝ _`;
  (ii) the character convention: `delta0NebentypusHChar χ (GL_adjugate h) _ = χ (Gamma0MapUnits g)`.

Gap (ii) is isolated as the convention bridge lemma `char_bridge`.
-/

/-- **Convention bridge lemma (the heart of the convention check).**
For `g ∈ Γ₀(N)`, embedded as `h = mapGL ℚ g ∈ (Gamma0_pair N).H`, the χ-coefficient
used by `IsGamma0TwistedInvariant` (= χ of the upper-left unit of `adj(h)`) equals the
χ-coefficient used by `modFormCharSpace`/`Gamma0MapUnits` (= χ of the lower-right unit
of `g`). Both reduce to `χ` evaluated at the lower-right entry of `g` mod `N`. -/
lemma char_bridge (χ : (ZMod N)ˣ →* ℂˣ) (g : ↥(Gamma0 N))
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

/-- **The "forget" direction.** An element of the diamond χ-eigenspace, viewed as a
function, satisfies the Γ₀(N)-twisted-slash condition. -/
theorem coe_mem_twistedInvariant
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
  rw [← char_bridge (N := N) χ g hmem]

/-! ## Packaging the twisted operator output as a `modFormCharSpace` element

For `f ∈ modFormCharSpace k χ`, `coe_mem_twistedInvariant` gives the
function-level invariance of `twistedHeckeSlash_gen k χ D (⇑f)`. This wraps that
function as a genuine `ModularForm`. The function `twistedHeckeSlash_gen` is a finite
ℂ-weighted sum of slashes of `⇑f`, so holomorphy and cusp-boundedness reduce to the
per-summand facts (holomorphy/boundedness of `f ∣[k] tRep_gen`, scaled).
-/

/-- **Bridge: function-level invariance ⇒ nebentypus relation over ℝ.**
The `IsGamma0TwistedInvariant` predicate is phrased over `glMap h` for `h ∈ (Gamma0_pair N).H`
(rational `GL₂`). Specializing to `h = mapGL ℚ g` for `g ∈ Γ₀(N)` and applying the convention
bridge `char_bridge`, this is exactly the classical nebentypus slash relation
`F ∣[k] mapGL ℝ g = χ(Gamma0MapUnits g) • F` used by `modFormCharSpace_iff_nebentypus`. -/
theorem twistedInvariant_nebentypus
    {k : ℤ} {χ : (ZMod N)ˣ →* ℂˣ} {F : ℍ → ℂ}
    (hF : IsGamma0TwistedInvariant (N := N) k χ F) (g : ↥(Gamma0 N)) :
    F ∣[k] (mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (g : SL(2, ℤ)) =
      (↑(χ (Gamma0MapUnits g)) : ℂ) • F := by
  have hmem : (mapGL ℚ (g : SL(2, ℤ)) : GL (Fin 2) ℚ) ∈ (Gamma0_pair N).H :=
    Subgroup.mem_map.mpr ⟨(g : SL(2, ℤ)), g.2, rfl⟩
  -- `glMap (mapGL ℚ g) = mapGL ℝ g`.
  have hgl : glMap (mapGL ℚ (g : SL(2, ℤ))) =
      (mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (g : SL(2, ℤ)) := by
    apply Units.ext; ext i j
    simp only [glMap, GeneralLinearGroup.map]
    exact (IsScalarTower.algebraMap_apply ℤ ℚ ℝ ((g : SL(2, ℤ)).1 i j)).symm
  have hinv := hF (mapGL ℚ (g : SL(2, ℤ))) hmem
  rw [hgl] at hinv
  rw [hinv, char_bridge (N := N) χ g hmem]

variable {k : ℤ} {χ : (ZMod N)ˣ →* ℂˣ}

/-- The underlying function `twistedHeckeSlash_gen k χ D (⇑f)` as an explicit finite sum,
exposing each summand `c⁻¹ • (⇑f ∣[k] tRep_gen D i)`. -/
private lemma twistedHeckeSlash_gen_eq_sum
    (D : HeckeCoset (Gamma0_pair N))
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    twistedHeckeSlash_gen (N := N) k χ D (⇑f) =
      ∑ i : decompQuot (Gamma0_pair N) (HeckeCoset.rep D),
        (↑(delta0NebentypusWeight (N := N) χ D i) : ℂ)⁻¹ •
          ((⇑f) ∣[k] tRep_gen (Gamma0_pair N) D i) := rfl

/-- Holomorphy of the twisted Hecke slash: a finite ℂ-weighted sum of slashes
of a modular form. -/
private lemma twistedHeckeSlash_gen_holomorphic
    (D : HeckeCoset (Gamma0_pair N))
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (twistedHeckeSlash_gen (N := N) k χ D (⇑f)) := by
  rw [twistedHeckeSlash_gen_eq_sum]
  exact MDifferentiable.sum fun i _ =>
    MDifferentiable.const_smul _ ((ModularFormClass.holo f).slash k _)

/-- A scaled slash of a modular form by a `Γ₀(N)` Hecke representative equals the slash
of the scaled modular form: `a • (f ∣[k] tRep) = (a • f) ∣[k] tRep`. This is used to push
the per-summand scalar of `twistedHeckeSlash_gen` onto the modular form, whose cusp-bound
is then available from `ModularForm.bdd_at_cusps'`. -/
private lemma smul_slash_tRep_gen_modForm
    (D : HeckeCoset (Gamma0_pair N))
    (i : decompQuot (Gamma0_pair N) (HeckeCoset.rep D))
    (a : ℂ) (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    a • ((⇑f) ∣[k] tRep_gen (Gamma0_pair N) D i) =
      ((a • ⇑f : ℍ → ℂ)) ∣[k] tRep_gen (Gamma0_pair N) D i := by
  have hσ : UpperHalfPlane.σ (glMap (tRep_gen (Gamma0_pair N) D i)) = RingHom.id ℂ := by
    unfold UpperHalfPlane.σ
    simp only [tRep_gen_Gamma0_det_pos (N := N) D i, ↓reduceIte]
  change a • ((⇑f) ∣[k] glMap (tRep_gen (Gamma0_pair N) D i)) =
    (a • ⇑f : ℍ → ℂ) ∣[k] glMap (tRep_gen (Gamma0_pair N) D i)
  rw [ModularForm.smul_slash, hσ]
  rfl

/-- Cusp-boundedness of the twisted Hecke slash: a finite ℂ-weighted sum of
slashes of a modular form, scaled. -/
private lemma twistedHeckeSlash_gen_bdd_at_cusps
    (D : HeckeCoset (Gamma0_pair N))
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    {c : OnePoint ℝ} (hc : IsCusp c ((Gamma1 N).map (mapGL ℝ))) :
    c.IsBoundedAt (twistedHeckeSlash_gen (N := N) k χ D (⇑f)) k := by
  rw [twistedHeckeSlash_gen_eq_sum]
  apply Finset.sum_induction _ (fun g => c.IsBoundedAt g k)
    (fun _ _ ha hb => ha.add hb)
    ((0 : ModularForm ((Gamma1 N).map (mapGL ℝ)) k).bdd_at_cusps' hc)
  intro i _
  -- Push the scalar onto the modular form, then use its cusp-bound.
  rw [smul_slash_tRep_gen_modForm (N := N) D i _ f,
    show ((↑(delta0NebentypusWeight (N := N) χ D i) : ℂ)⁻¹ • ⇑f : ℍ → ℂ) =
      ⇑((↑(delta0NebentypusWeight (N := N) χ D i) : ℂ)⁻¹ • f) from rfl]
  exact OnePoint.IsBoundedAt.smul_iff.mp
    (((↑(delta0NebentypusWeight (N := N) χ D i) : ℂ)⁻¹ • f).bdd_at_cusps'
      (HeckeRing.GL2.glMap_smul_isCusp_Gamma1 _ hc))

/-- **Packaging form.** The twisted Hecke operator output, packaged as a
`ModularForm` at the `Γ₁(N)`-level. Holomorphy and cusp-boundedness come from the
per-summand facts; `Γ₁(N)`-invariance comes from `coe_mem_twistedInvariant`
specialized to `Γ₁(N)` (where the nebentypus character is trivial). -/
noncomputable def nebentypusHeckeOpModularForm
    (D : HeckeCoset (Gamma0_pair N))
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) (hf : f ∈ modFormCharSpace k χ) :
    ModularForm ((Gamma1 N).map (mapGL ℝ)) k where
  toFun := twistedHeckeSlash_gen (N := N) k χ D (⇑f)
  slash_action_eq' γ hγ := by
    -- Γ₁ ≤ Γ₀, and on Γ₁ the nebentypus character is `1`, so the relation is invariance.
    obtain ⟨σ, hσ_Gamma1, rfl⟩ := Subgroup.mem_map.mp hγ
    have hσ_Gamma0 : σ ∈ Gamma0 N := Gamma1_le_Gamma0 N hσ_Gamma1
    have h_units : Gamma0MapUnits (⟨σ, hσ_Gamma0⟩ : ↥(Gamma0 N)) = 1 := by
      have h := (Gamma1_mem N σ).mp hσ_Gamma1
      ext
      simp only [Gamma0MapUnits_val, Gamma0Map, MonoidHom.coe_mk, OneHom.coe_mk,
        Units.val_one]
      exact h.2.1
    have hneb := twistedInvariant_nebentypus
      (coe_mem_twistedInvariant f hf
        |> twistedHeckeSlash_gen_preserves_invariant (N := N) k χ D (⇑f))
      ⟨σ, hσ_Gamma0⟩
    rw [h_units, map_one, Units.val_one, one_smul] at hneb
    exact hneb
  holo' := twistedHeckeSlash_gen_holomorphic D f
  bdd_at_cusps' hc := twistedHeckeSlash_gen_bdd_at_cusps D f hc

@[simp] lemma nebentypusHeckeOpModularForm_coe
    (D : HeckeCoset (Gamma0_pair N))
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) (hf : f ∈ modFormCharSpace k χ) :
    (⇑(nebentypusHeckeOpModularForm (N := N) D f hf) : ℍ → ℂ) =
      twistedHeckeSlash_gen (N := N) k χ D (⇑f) := rfl

/-- **Membership.** The packaged twisted Hecke operator output lies in the
character space `modFormCharSpace k χ`. -/
theorem nebentypusHeckeOpModularForm_mem
    (D : HeckeCoset (Gamma0_pair N))
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) (hf : f ∈ modFormCharSpace k χ) :
    nebentypusHeckeOpModularForm (N := N) D f hf ∈ modFormCharSpace k χ := by
  rw [modFormCharSpace_iff_nebentypus]
  intro g
  rw [nebentypusHeckeOpModularForm_coe]
  exact twistedInvariant_nebentypus
    (coe_mem_twistedInvariant f hf
      |> twistedHeckeSlash_gen_preserves_invariant (N := N) k χ D (⇑f)) g

/-! ## The per-coset linear operator on `modFormCharSpace k χ`

The packaging maps assemble into a `ℂ`-linear endomorphism of the character space.
Linearity is inherited from additivity/`ℂ`-homogeneity of `twistedHeckeSlash_gen`
(`twistedHeckeSlash_gen_add`, `twistedHeckeSlash_gen_smul`) via injectivity of the
coercion `modFormCharSpace k χ ↪ (ℍ → ℂ)`. -/

/-- The packaged twisted Hecke operator as an element of `modFormCharSpace k χ`,
viewed as the subtype `↥(modFormCharSpace k χ)`. -/
noncomputable def nebentypusHeckeOp
    (D : HeckeCoset (Gamma0_pair N))
    (f : modFormCharSpace k χ) : modFormCharSpace k χ :=
  let g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k := (f : ModularForm _ k)
  let hg : g ∈ modFormCharSpace k χ := f.2
  ⟨nebentypusHeckeOpModularForm D g hg, nebentypusHeckeOpModularForm_mem D g hg⟩

/-- The underlying `ModularForm` of `nebentypusHeckeOp D f` is `nebentypusHeckeOpModularForm`. -/
@[simp] lemma nebentypusHeckeOp_coe
    (D : HeckeCoset (Gamma0_pair N))
    (f : modFormCharSpace k χ) :
    (nebentypusHeckeOp D f : ModularForm _ k) =
      nebentypusHeckeOpModularForm D (f : ModularForm _ k) f.2 := rfl

/-- The underlying `ModularForm` of `nebentypusHeckeOp D f` is `nebentypusHeckeOpModularForm`. -/
@[simp] lemma nebentypusHeckeOp_val
    (D : HeckeCoset (Gamma0_pair N))
    (f : modFormCharSpace k χ) :
    ((nebentypusHeckeOp D f : modFormCharSpace k χ) :
        ModularForm ((Gamma1 N).map (mapGL ℝ)) k) =
      nebentypusHeckeOpModularForm D
        (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) f.2 := rfl

/-- The underlying function of `nebentypusHeckeOp D f` is the twisted Hecke slash of `⇑f`. -/
@[simp] lemma nebentypusHeckeOp_coe_coe
    (D : HeckeCoset (Gamma0_pair N))
    (f : modFormCharSpace k χ) (z : ℍ) :
    ((nebentypusHeckeOp D f : modFormCharSpace k χ) :
        ModularForm ((Gamma1 N).map (mapGL ℝ)) k) z =
      twistedHeckeSlash_gen (N := N) k χ D
        (⇑(f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)) z := rfl

/-- The twisted Hecke double-coset operator as a `ℂ`-linear endomorphism
of the character space `modFormCharSpace k χ`. -/
noncomputable def nebentypusHeckeOpLinear
    (D : HeckeCoset (Gamma0_pair N)) :
    modFormCharSpace k χ →ₗ[ℂ] modFormCharSpace k χ where
  toFun f := nebentypusHeckeOp D f
  map_add' f g := by
    apply Subtype.ext
    apply ModularForm.ext
    intro z
    -- Both sides reduce to `twistedHeckeSlash_gen` of `⇑↑f + ⇑↑g`, using additivity.
    simp only [nebentypusHeckeOp_coe_coe, Submodule.coe_add, ModularForm.add_apply,
      ModularForm.coe_add, twistedHeckeSlash_gen_add, Pi.add_apply]
  map_smul' c f := by
    apply Subtype.ext
    apply ModularForm.ext
    intro z
    rw [nebentypusHeckeOp_coe_coe, Submodule.coe_smul,
      show (⇑(c • (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k))) =
        c • ⇑(f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) from rfl,
      twistedHeckeSlash_gen_smul]
    simp [Pi.smul_apply]

@[simp] lemma nebentypusHeckeOpLinear_apply
    (D : HeckeCoset (Gamma0_pair N)) (f : modFormCharSpace k χ) :
    nebentypusHeckeOpLinear D f = nebentypusHeckeOp D f := rfl

/-! ## Assembling `Φ_χ` over the Hecke ring `𝕋 (Gamma0_pair N) ℤ`

We extend the per-coset operators `nebentypusHeckeOpLinear D` by `ℤ`-linearity to a
ring homomorphism `𝕋 (Gamma0_pair N) ℤ →+* Module.End ℂ (modFormCharSpace k χ)`,
mirroring `twistedHeckeSumFunction`/`twistedHeckeRingHomFunction` at the
`ModularForm` level. The ring axioms transport from the already-proven
function-level facts via injectivity of the coercion `modFormCharSpace k χ ↪ (ℍ → ℂ)`.
-/

/-- The `ℤ`-linear extension of the per-coset operators `nebentypusHeckeOpLinear` over the
existing Hecke ring `𝕋 (Gamma0_pair N) ℤ`, valued in `Module.End ℂ (modFormCharSpace k χ)`.
This is the candidate `Φ_χ`. -/
noncomputable def nebentypusHeckeSum
    (T : 𝕋 (Gamma0_pair N) ℤ) :
    Module.End ℂ (modFormCharSpace k χ) :=
  T.sum (fun D c ↦ (c : ℂ) • nebentypusHeckeOpLinear (N := N) (k := k) (χ := χ) D)

@[simp] lemma nebentypusHeckeSum_zero :
    nebentypusHeckeSum (N := N) (k := k) (χ := χ) (0 : 𝕋 (Gamma0_pair N) ℤ) = 0 := by
  simp [nebentypusHeckeSum]

@[simp] lemma nebentypusHeckeSum_T_single
    (D : HeckeCoset (Gamma0_pair N)) (c : ℤ) :
    nebentypusHeckeSum (N := N) (k := k) (χ := χ) (T_single (Gamma0_pair N) ℤ D c) =
      (c : ℂ) • nebentypusHeckeOpLinear (N := N) (k := k) (χ := χ) D := by
  simp [nebentypusHeckeSum, T_single]

lemma nebentypusHeckeSum_add
    (T₁ T₂ : 𝕋 (Gamma0_pair N) ℤ) :
    nebentypusHeckeSum (N := N) (k := k) (χ := χ) (T₁ + T₂) =
      nebentypusHeckeSum (N := N) (k := k) (χ := χ) T₁ +
        nebentypusHeckeSum (N := N) (k := k) (χ := χ) T₂ := by
  dsimp [nebentypusHeckeSum]
  rw [Finsupp.sum_add_index']
  · intro D
    simp
  · intro D c₁ c₂
    ext f
    simp [add_smul]

/-- **Compatibility with the function-level extension.** Applying `Φ_χ` to a form `f`
and coercing to a function reproduces the proven function-valued weighted extension
`twistedHeckeSlashExt_gen` of `⇑f`. This is the bridge that transports the ring axioms
(`map_one`, `map_mul`) from the function level to the `ModularForm` level. -/
lemma nebentypusHeckeSum_apply_coe
    (T : 𝕋 (Gamma0_pair N) ℤ)
    (f : modFormCharSpace k χ) :
    (⇑((nebentypusHeckeSum (N := N) (k := k) (χ := χ) T f :
        modFormCharSpace k χ) :
        ModularForm ((Gamma1 N).map (mapGL ℝ)) k) : ℍ → ℂ) =
      twistedHeckeSlashExt_gen (N := N) k χ T
        (⇑(f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)) := by
  induction T using Finsupp.induction_linear with
  | zero =>
      simp [nebentypusHeckeSum, twistedHeckeSlashExt_gen]
  | add T₁ T₂ h₁ h₂ =>
      rw [nebentypusHeckeSum_add, twistedHeckeSlashExt_gen_add]
      funext z
      have e₁ := congrFun h₁ z
      have e₂ := congrFun h₂ z
      simp only [LinearMap.add_apply, Submodule.coe_add, ModularForm.add_apply,
        Pi.add_apply]
      rw [e₁, e₂]
  | single D c =>
      rw [nebentypusHeckeSum_T_single]
      funext z
      unfold twistedHeckeSlashExt_gen
      rw [Finsupp.sum_single_index (by simp :
        (0 : ℤ) • twistedHeckeSlash_gen (N := N) k χ D
          (⇑(f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)) = 0)]
      -- LHS: `⇑↑((c • nebentypusHeckeOpLinear D) f) z`;
      -- RHS: `(c : ℤ) • twistedHeckeSlash_gen ... z`.
      simp [LinearMap.smul_apply, nebentypusHeckeOpLinear_apply, SetLike.val_smul]

/-- The underlying function of `⇑f` (for `f : modFormCharSpace k χ`), packaged as an
element of the function-level twisted-invariant submodule via `coe_mem_twistedInvariant`. -/
noncomputable def nebentypusToFunctionSubmodule
    (f : modFormCharSpace k χ) :
    gamma0TwistedInvariantFunctionSubmodule (N := N) k χ :=
  ⟨⇑(f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k),
    coe_mem_twistedInvariant
      (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) f.2⟩

/-- The function underlying `Φ_χ T f` equals the function-valued ring action
`twistedHeckeSumFunction` applied to `⇑f`. This rephrases `nebentypusHeckeSum_apply_coe`
through the (already-proven) function-level ring homomorphism. -/
lemma nebentypusHeckeSum_coe_eq_twistedHeckeSumFunction
    (T : 𝕋 (Gamma0_pair N) ℤ) (f : modFormCharSpace k χ) :
    (⇑((nebentypusHeckeSum (N := N) (k := k) (χ := χ) T f :
        modFormCharSpace k χ) :
        ModularForm ((Gamma1 N).map (mapGL ℝ)) k) : ℍ → ℂ) =
      (twistedHeckeSumFunction (N := N) k χ T
        (nebentypusToFunctionSubmodule (N := N) f) : ℍ → ℂ) := by
  rw [nebentypusHeckeSum_apply_coe, twistedHeckeSumFunction_apply_coe]
  rfl

/-- The "transport-to-functions" map `nebentypusToFunctionSubmodule` intertwines the
`ModularForm`-level operator `Φ_χ T` (`nebentypusHeckeSum`) with the function-level operator
`twistedHeckeSumFunction T`. This is the multiplicativity-compatible form of the bridge. -/
lemma nebentypusToFunctionSubmodule_heckeSum
    (T : 𝕋 (Gamma0_pair N) ℤ) (f : modFormCharSpace k χ) :
    nebentypusToFunctionSubmodule (N := N)
        (nebentypusHeckeSum (N := N) (k := k) (χ := χ) T f) =
      twistedHeckeSumFunction (N := N) k χ T (nebentypusToFunctionSubmodule (N := N) f) := by
  apply Subtype.ext
  -- Both `.val`s are functions; reduce to the proven coercion bridge.
  change (⇑((nebentypusHeckeSum (N := N) (k := k) (χ := χ) T f :
      modFormCharSpace k χ) :
      ModularForm ((Gamma1 N).map (mapGL ℝ)) k) : ℍ → ℂ) =
    (twistedHeckeSumFunction (N := N) k χ T (nebentypusToFunctionSubmodule (N := N) f) :
      ℍ → ℂ)
  rw [nebentypusHeckeSum_coe_eq_twistedHeckeSumFunction]

/-- **`Φ_χ` as a ring homomorphism.** The `Γ₀(N)` Hecke ring acts
on the nebentypus character space `modFormCharSpace k χ` by a genuine ring homomorphism
`𝕋(Γ₀(N)) →+* End_ℂ (Mₖ(Γ₁(N), χ))`. The ring
axioms transport from the proven function-level homomorphism `twistedHeckeRingHomFunction`
via the coercion-injectivity bridge `nebentypusHeckeSum_coe_eq_twistedHeckeSumFunction`. -/
noncomputable def heckeRingHomCharSpace :
    𝕋 (Gamma0_pair N) ℤ →+* Module.End ℂ (modFormCharSpace k χ) where
  toFun := nebentypusHeckeSum (N := N) (k := k) (χ := χ)
  map_zero' := nebentypusHeckeSum_zero
  map_add' := nebentypusHeckeSum_add
  map_one' := by
    refine LinearMap.ext fun f => ?_
    apply Subtype.ext
    apply DFunLike.coe_injective
    dsimp only
    rw [show (1 : 𝕋 (Gamma0_pair N) ℤ) = T_single (Gamma0_pair N) ℤ
      (HeckeCoset.one (Gamma0_pair N)) 1 from HeckeRing.one_def _ _]
    rw [nebentypusHeckeSum_coe_eq_twistedHeckeSumFunction]
    rw [show T_single (Gamma0_pair N) ℤ (HeckeCoset.one (Gamma0_pair N)) 1 =
      (1 : 𝕋 (Gamma0_pair N) ℤ) from (HeckeRing.one_def _ _).symm]
    rw [twistedHeckeSumFunction_one]
    rfl
  map_mul' T₁ T₂ := by
    refine LinearMap.ext fun f => ?_
    apply Subtype.ext
    apply DFunLike.coe_injective
    dsimp only
    rw [nebentypusHeckeSum_coe_eq_twistedHeckeSumFunction, twistedHeckeSumFunction_mul]
    -- RHS is `(nebentypusHeckeSum T₁ * nebentypusHeckeSum T₂) f`; unfold the End-product.
    show (twistedHeckeSumFunction (N := N) k χ T₁ *
        twistedHeckeSumFunction (N := N) k χ T₂)
        (nebentypusToFunctionSubmodule (N := N) f) =
      ⇑((nebentypusHeckeSum (N := N) (k := k) (χ := χ) T₁
        (nebentypusHeckeSum (N := N) (k := k) (χ := χ) T₂ f)) :
        ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    rw [Module.End.mul_apply, nebentypusHeckeSum_coe_eq_twistedHeckeSumFunction,
      nebentypusToFunctionSubmodule_heckeSum]

/-! ## The good-prime bridge: `heckeRingHomCharSpace (T_single D_p 1)` vs `heckeT_p_all`

The canonical χ-twisted operator `heckeRingHomCharSpace` applied to the prime
double coset `D_p_Gamma0` reproduces the concrete operator `heckeT_p_all` on the
character space.  Everything below is reconstructed from public lemmas (the bijection
helpers in `HeckeT_p_Gamma0_Bridge.lean` are `private`, so we rebuild the analogue here
with the χ-weights of `twistedHeckeSlash_gen`).
-/

section Bridge

variable {k : ℤ} {χ : (ZMod N)ˣ →* ℂˣ}

/-- `adj(rep(D_p_Gamma0)) ∈ D_p_Gamma0` (public reconstruction of the private
`adj_rep_mem_D_p_Gamma0_bridge`). The double coset of `diag(1,p)` is stable under
adjugation because `adj(diag(1,p)) = T_p_lower ∈ D_p_Gamma0`. -/
private lemma adj_rep_mem (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) :
    GL_adjugate (HeckeCoset.rep (D_p_Gamma0 N p hp.pos) : GL _ ℚ) ∈
      HeckeCoset.toSet (D_p_Gamma0 N p hp.pos) := by
  have hrep := HeckeCoset.rep_mem (D_p_Gamma0 N p hp.pos)
  rw [D_p_Gamma0, diag_1p_delta_Gamma0, HeckeCoset.toSet_mk,
    DoubleCoset.mem_doubleCoset] at hrep
  obtain ⟨a, ha, c, hc, hrep_eq⟩ := hrep
  have hTl := T_p_lower_mem_D_p_Gamma0 N p hp hpN
  rw [HeckeCoset.toSet_eq_rep, DoubleCoset.mem_doubleCoset] at hTl
  obtain ⟨b₁, hb₁, b₂, hb₂, hTl_eq⟩ := hTl
  rw [HeckeCoset.toSet_eq_rep, DoubleCoset.mem_doubleCoset]
  refine ⟨GL_adjugate c * b₁,
    (Gamma0_pair N).H.mul_mem (HeckePairAction.adjugate_mem_H c hc) hb₁,
    b₂ * GL_adjugate a,
    (Gamma0_pair N).H.mul_mem hb₂ (HeckePairAction.adjugate_mem_H a ha), ?_⟩
  -- `adj(diag(1,p)) = T_p_lower`.
  have hadj_diag : GL_adjugate (diagMat 2 ![1, p] : GL (Fin 2) ℚ) =
      (T_p_lower p hp.pos : GL (Fin 2) ℚ) := by
    apply Units.ext; ext i j
    have hpos : ∀ m : Fin 2, 0 < (![1, p] : Fin 2 → Nat) m := fun m => by
      fin_cases m <;> simp [hp.pos]
    simp only [GL_adjugate_val, diagMat_val _ _ hpos]
    have huniv : (Finset.univ : Finset (Fin 2)) = {0, 1} := by
      ext x; fin_cases x <;> simp
    have he0 : ({0, 1} : Finset (Fin 2)).erase 0 = {1} := by decide
    have he1 : ({0, 1} : Finset (Fin 2)).erase 1 = {0} := by decide
    fin_cases i <;> fin_cases j <;>
      simp [T_p_lower, GeneralLinearGroup.mkOfDetNeZero,
        Matrix.of_apply, huniv, he0, he1, Finset.prod_singleton]
  have h1 : GL_adjugate (HeckeCoset.rep (D_p_Gamma0 N p hp.pos) : GL _ ℚ) =
      GL_adjugate c * GL_adjugate (diagMat 2 ![1, p]) * GL_adjugate a := by
    conv_lhs => rw [show (HeckeCoset.rep (D_p_Gamma0 N p hp.pos) : GL _ ℚ) =
      a * diagMat 2 ![1, p] * c from hrep_eq]
    rw [GL_adjugate_mul, GL_adjugate_mul, mul_assoc]
  rw [h1, hadj_diag, hTl_eq]; group

/-- For `g ∈ D_p_Gamma0`, the adjugate factorises through the rep with `H`-factors
(public reconstruction of the private `adj_mem_dc_factorisation_Gamma0_bridge`). -/
private lemma adj_factorisation (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) (g : GL (Fin 2) ℚ)
    (hg : g ∈ HeckeCoset.toSet (D_p_Gamma0 N p hp.pos)) :
    ∃ (h₁ : GL (Fin 2) ℚ) (_ : h₁ ∈ (Gamma0_pair N).H)
      (h₂ : GL (Fin 2) ℚ) (_ : h₂ ∈ (Gamma0_pair N).H),
      GL_adjugate g =
        h₁ * (HeckeCoset.rep (D_p_Gamma0 N p hp.pos) : GL _ ℚ) * h₂ := by
  -- `adj` preserves the double coset: if `g = a·rep·c` then `adj g = adj c·adj rep·adj a`,
  -- and `adj rep ∈ D_p_Gamma0` by `adj_rep_mem`.
  have hadj_rep := adj_rep_mem p hp hpN
  rw [HeckeCoset.toSet_eq_rep, DoubleCoset.mem_doubleCoset] at hg hadj_rep
  obtain ⟨a, ha, c, hc, heq⟩ := hg
  obtain ⟨r₁, hr₁, r₂, hr₂, hrep_eq⟩ := hadj_rep
  refine ⟨GL_adjugate c * r₁,
    (Gamma0_pair N).H.mul_mem (HeckePairAction.adjugate_mem_H c hc) hr₁,
    r₂ * GL_adjugate a,
    (Gamma0_pair N).H.mul_mem hr₂ (HeckePairAction.adjugate_mem_H a ha), ?_⟩
  rw [heq, GL_adjugate_mul, GL_adjugate_mul]
  rw [show GL_adjugate (HeckeCoset.rep (D_p_Gamma0 N p hp.pos) : GL _ ℚ) =
    r₁ * (HeckeCoset.rep (D_p_Gamma0 N p hp.pos) : GL _ ℚ) * r₂ from hrep_eq]
  group

/-- `delta0NebentypusDeltaChar` depends only on the underlying `GL (Fin 2) ℚ` value. -/
private lemma delta0Char_congr (χ : (ZMod N)ˣ →* ℂˣ)
    (g₁ g₂ : (Gamma0_pair N).Δ) (h : (g₁ : GL (Fin 2) ℚ) = (g₂ : GL (Fin 2) ℚ)) :
    delta0NebentypusDeltaChar (N := N) χ g₁ =
      delta0NebentypusDeltaChar (N := N) χ g₂ := by
  apply congrArg (delta0NebentypusDeltaChar (N := N) χ); exact Subtype.ext h

/-- The weighted value equality at an explicit factorisation: if `adj(g) = h₁·rep·h₂`
with `h₁,h₂ ∈ Γ₀(N)` and `gΔ` is a `Δ₀(N)`-element with matrix `adj(g)`, then the χ-weighted
slash by `g` equals the χ-weighted `tRep_gen` summand at the class `⟦⟨h₁,hh₁⟩⟧`. Packaged
via `gamma0TripleDelta`, so `twisted_weighted_slash_tRep_gen_of_mem` applies. -/
private lemma weighted_value_eq (p : ℕ) (hp : Nat.Prime p)
    {f : ℍ → ℂ} (hf : IsGamma0TwistedInvariant (N := N) k χ f)
    (g : GL (Fin 2) ℚ)
    (gΔ : (Gamma0_pair N).Δ)
    (h₁ : GL (Fin 2) ℚ) (hh₁ : h₁ ∈ (Gamma0_pair N).H)
    (h₂ : GL (Fin 2) ℚ) (hh₂ : h₂ ∈ (Gamma0_pair N).H)
    (hadj : GL_adjugate g = h₁ * (HeckeCoset.rep (D_p_Gamma0 N p hp.pos) : GL _ ℚ) * h₂)
    (hgΔ : (gΔ : GL (Fin 2) ℚ) = GL_adjugate g) :
    ((↑(delta0NebentypusDeltaChar (N := N) χ gΔ) : ℂ)⁻¹) • (f ∣[k] g) =
      ((↑(delta0NebentypusWeight (N := N) χ (D_p_Gamma0 N p hp.pos)
          ⟦⟨h₁, hh₁⟩⟧) : ℂ)⁻¹) •
        (f ∣[k] tRep_gen (Gamma0_pair N) (D_p_Gamma0 N p hp.pos) ⟦⟨h₁, hh₁⟩⟧) := by
  set D := D_p_Gamma0 N p hp.pos with hD
  -- `g = adj(adj g) = adj(h₁ rep h₂)`.
  have hg_eq : g = GL_adjugate (h₁ * (HeckeCoset.rep D : GL _ ℚ) * h₂) := by
    rw [← hadj, GL_adjugate_involutive]
  -- Match the LHS weight: `δ₀(gΔ) = δ₀(gamma0TripleDelta D h₁ h₂)` (same matrix `adj g`).
  have hweight : delta0NebentypusDeltaChar (N := N) χ gΔ =
      delta0NebentypusDeltaChar (N := N) χ
        (gamma0TripleDelta (N := N) D h₁ hh₁ h₂ hh₂) := by
    apply delta0Char_congr
    change (gΔ : GL (Fin 2) ℚ) = h₁ * (HeckeCoset.rep D : GL _ ℚ) * h₂
    rw [hgΔ, hadj]
  rw [hweight, hg_eq]
  exact twisted_weighted_slash_tRep_gen_of_mem (N := N) k χ D h₁ hh₁ h₂ hh₂ f hf

/-- `adj(T_p_upper b)` as a `Δ₀(N)` element (matrix `!![p,-b;0,1]`). Needs `p` coprime
to `N` because the upper-left entry of the adjugate is `p`. -/
private noncomputable def adjUpperΔ (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) (b : ℕ) : (Gamma0_pair N).Δ := by
  refine ⟨GL_adjugate (T_p_upper p hp.pos b), ?_⟩
  set A : Matrix (Fin 2) (Fin 2) ℤ := !![(p : ℤ), -(b : ℤ); 0, 1]
  have hA_eq : ((GL_adjugate (T_p_upper p hp.pos b) : GL (Fin 2) ℚ) :
      Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ) := by
    rw [GL_adjugate_val, T_p_upper_coe, Matrix.adjugate_fin_two]
    ext i j; fin_cases i <;> fin_cases j <;> simp [A]
  refine ⟨⟨A, hA_eq⟩, ?_, A, hA_eq, ?_, ?_⟩
  · rw [GL_adjugate_val, Matrix.det_adjugate, Fintype.card_fin, T_p_upper_coe]
    simp only [det_fin_two_of]; push_cast; ring_nf; exact_mod_cast hp.pos
  · simp [A]
  · simpa [A] using hpN

/-- `adj(T_p_lower)` as a `Δ₀(N)` element (matrix `!![1,0;0,p]`). -/
private noncomputable def adjLowerΔ (p : ℕ) (hp : Nat.Prime p) :
    (Gamma0_pair N).Δ := by
  refine ⟨GL_adjugate (T_p_lower p hp.pos), ?_⟩
  set A : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 0, (p : ℤ)]
  have hA_eq : ((GL_adjugate (T_p_lower p hp.pos) : GL (Fin 2) ℚ) :
      Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ) := by
    rw [GL_adjugate_val, T_p_lower_coe, Matrix.adjugate_fin_two]
    ext i j; fin_cases i <;> fin_cases j <;> simp [A]
  refine ⟨⟨A, hA_eq⟩, ?_, A, hA_eq, ?_, ?_⟩
  · rw [GL_adjugate_val, Matrix.det_adjugate, Fintype.card_fin, T_p_lower_coe]
    simp only [det_fin_two_of]; push_cast; ring_nf; exact_mod_cast hp.pos
  · simp [A]
  · simp [A]

@[simp] private lemma adjUpperΔ_coe (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) (b : ℕ) :
    (adjUpperΔ (N := N) p hp hpN b : GL (Fin 2) ℚ) =
      GL_adjugate (T_p_upper p hp.pos b) := rfl

@[simp] private lemma adjLowerΔ_coe (p : ℕ) (hp : Nat.Prime p) :
    (adjLowerΔ (N := N) p hp : GL (Fin 2) ℚ) =
      GL_adjugate (T_p_lower p hp.pos) := rfl

/-- Weight at the upper representative: `δ₀(adj(T_p_upper b)) = χ(p mod N)`. -/
private lemma adjUpperΔ_weight (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) (b : ℕ) :
    delta0NebentypusDeltaChar (N := N) χ (adjUpperΔ (N := N) p hp hpN b) =
      χ (ZMod.unitOfCoprime p hpN) := by
  unfold delta0NebentypusDeltaChar
  simp only [MonoidHom.coe_mk, OneHom.coe_mk]
  congr 1
  apply Units.ext
  rw [Delta0UpperUnit_val, ZMod.coe_unitOfCoprime]
  -- The integer witness has `(0,0)`-entry `p`.
  have hwit : delta0IntegralMatrix (N := N) (adjUpperΔ (N := N) p hp hpN b) =
      !![(p : ℤ), -(b : ℤ); 0, 1] := by
    apply delta0IntegralMatrix_witness_unique
    rw [adjUpperΔ_coe, GL_adjugate_val, T_p_upper_coe, Matrix.adjugate_fin_two]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [hwit]; simp

/-- Weight at the lower representative: `δ₀(adj(T_p_lower)) = χ(1) = 1`. -/
private lemma adjLowerΔ_weight (p : ℕ) (hp : Nat.Prime p) :
    delta0NebentypusDeltaChar (N := N) χ (adjLowerΔ (N := N) p hp) = 1 := by
  unfold delta0NebentypusDeltaChar
  simp only [MonoidHom.coe_mk, OneHom.coe_mk]
  rw [show (1 : ℂˣ) = χ 1 from (map_one χ).symm]
  congr 1
  apply Units.ext
  rw [Delta0UpperUnit_val, Units.val_one]
  have hwit : delta0IntegralMatrix (N := N) (adjLowerΔ (N := N) p hp) =
      !![1, 0; 0, (p : ℤ)] := by
    apply delta0IntegralMatrix_witness_unique
    rw [adjLowerΔ_coe, GL_adjugate_val, T_p_lower_coe, Matrix.adjugate_fin_two]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [hwit]; simp

/-- Adjugate factorisation of the upper representative `T_p_upper b` through the prime
double-coset representative, packaged as the existence statement used to index the
`decompQuot` permutation. -/
private lemma adj_T_p_upper_factorisation (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) (b : ℕ) :
    ∃ (h₁ : GL (Fin 2) ℚ) (_ : h₁ ∈ (Gamma0_pair N).H)
      (h₂ : GL (Fin 2) ℚ) (_ : h₂ ∈ (Gamma0_pair N).H),
      GL_adjugate (T_p_upper p hp.pos b : GL (Fin 2) ℚ) =
        h₁ * (HeckeCoset.rep (D_p_Gamma0 N p hp.pos) : GL _ ℚ) * h₂ :=
  adj_factorisation p hp hpN _ (T_p_upper_mem_D_p_Gamma0 N p hp b)

/-- Adjugate factorisation of the lower representative `T_p_lower` through the prime
double-coset representative. -/
private lemma adj_T_p_lower_factorisation (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) :
    ∃ (h₁ : GL (Fin 2) ℚ) (_ : h₁ ∈ (Gamma0_pair N).H)
      (h₂ : GL (Fin 2) ℚ) (_ : h₂ ∈ (Gamma0_pair N).H),
      GL_adjugate (T_p_lower p hp.pos : GL (Fin 2) ℚ) =
        h₁ * (HeckeCoset.rep (D_p_Gamma0 N p hp.pos) : GL _ ℚ) * h₂ :=
  adj_factorisation p hp hpN _ (T_p_lower_mem_D_p_Gamma0 N p hp hpN)

/-- The index map `Fin (p+1) → decompQuot` sending each classical `T_p` representative to
the `⟦h₁⟧`-class of its adjugate factorisation through the prime double-coset rep. -/
private noncomputable def twistedTpPsi (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) :
    Fin (p + 1) → decompQuot (Gamma0_pair N) (HeckeCoset.rep (D_p_Gamma0 N p hp.pos)) :=
  fun j =>
    if _h : j.val < p then
      ⟦⟨(adj_T_p_upper_factorisation (N := N) p hp hpN j.val).choose,
        (adj_T_p_upper_factorisation (N := N) p hp hpN j.val).choose_spec.choose⟩⟧
    else
      ⟦⟨(adj_T_p_lower_factorisation (N := N) p hp hpN).choose,
        (adj_T_p_lower_factorisation (N := N) p hp hpN).choose_spec.choose⟩⟧

/-- A quotient equality of `⟦h₁⟧`-classes for two factorisations `adj gᵢ = aᵢ·rep·cᵢ`
forces the adjugate ratio `(adj g₁)⁻¹·adj g₂` into `H`. -/
private lemma adj_quot_eq_imp_inv_mul_mem_H (g : (Gamma0_pair N).Δ)
    (a₁ : GL (Fin 2) ℚ) (ha₁ : a₁ ∈ (Gamma0_pair N).H)
    (c₁ : GL (Fin 2) ℚ) (hc₁ : c₁ ∈ (Gamma0_pair N).H)
    (a₂ : GL (Fin 2) ℚ) (ha₂ : a₂ ∈ (Gamma0_pair N).H)
    (c₂ : GL (Fin 2) ℚ) (hc₂ : c₂ ∈ (Gamma0_pair N).H)
    (g₁ g₂ : GL (Fin 2) ℚ)
    (heq₁ : GL_adjugate g₁ = a₁ * (g : GL (Fin 2) ℚ) * c₁)
    (heq₂ : GL_adjugate g₂ = a₂ * (g : GL (Fin 2) ℚ) * c₂)
    (hquot : (⟦(⟨a₁, ha₁⟩ : (Gamma0_pair N).H)⟧ :
        decompQuot (Gamma0_pair N) g) = ⟦⟨a₂, ha₂⟩⟧) :
    (GL_adjugate g₁)⁻¹ * GL_adjugate g₂ ∈ (Gamma0_pair N).H := by
  rw [heq₁, heq₂]
  have hrel := QuotientGroup.leftRel_apply.mp (Quotient.exact hquot)
  rw [Subgroup.mem_subgroupOf] at hrel
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hrel
  simp only [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct, map_inv, inv_inv] at hrel
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hrel
  have h_prod : (a₁ * (g : GL (Fin 2) ℚ) * c₁)⁻¹ * (a₂ * (g : GL (Fin 2) ℚ) * c₂) =
      c₁⁻¹ * (((g : GL (Fin 2) ℚ))⁻¹ * (a₁⁻¹ * a₂) * (g : GL (Fin 2) ℚ)) * c₂ := by group
  rw [h_prod]
  exact (Gamma0_pair N).H.mul_mem
    ((Gamma0_pair N).H.mul_mem ((Gamma0_pair N).H.inv_mem hc₁) hrel) hc₂

/-- Accessor wrapper for `adj_quot_eq_imp_inv_mul_mem_H`: feeds the four components of two
factorisation existence witnesses and the `⟦·⟧`-class equality of their chosen `h₁`'s. -/
private lemma adj_inv_mul_mem_H_of_factorisations (g : (Gamma0_pair N).Δ)
    (g₁ g₂ : GL (Fin 2) ℚ)
    (e₁ : ∃ (h₁ : GL (Fin 2) ℚ) (_ : h₁ ∈ (Gamma0_pair N).H) (h₂ : GL (Fin 2) ℚ)
        (_ : h₂ ∈ (Gamma0_pair N).H), GL_adjugate g₁ = h₁ * (g : GL (Fin 2) ℚ) * h₂)
    (e₂ : ∃ (h₁ : GL (Fin 2) ℚ) (_ : h₁ ∈ (Gamma0_pair N).H) (h₂ : GL (Fin 2) ℚ)
        (_ : h₂ ∈ (Gamma0_pair N).H), GL_adjugate g₂ = h₁ * (g : GL (Fin 2) ℚ) * h₂)
    (hquot : (⟦⟨e₁.choose, e₁.choose_spec.choose⟩⟧ : decompQuot (Gamma0_pair N) g)
        = ⟦⟨e₂.choose, e₂.choose_spec.choose⟩⟧) :
    (GL_adjugate g₁)⁻¹ * GL_adjugate g₂ ∈ (Gamma0_pair N).H :=
  adj_quot_eq_imp_inv_mul_mem_H g
    e₁.choose e₁.choose_spec.choose e₁.choose_spec.choose_spec.choose
      e₁.choose_spec.choose_spec.choose_spec.choose
    e₂.choose e₂.choose_spec.choose e₂.choose_spec.choose_spec.choose
      e₂.choose_spec.choose_spec.choose_spec.choose
    g₁ g₂ e₁.choose_spec.choose_spec.choose_spec.choose_spec
    e₂.choose_spec.choose_spec.choose_spec.choose_spec hquot

/-- The index map `twistedTpPsi` is injective: distinct classical `T_p` representatives land
in distinct `decompQuot` classes, by the `Γ₀(N)` distinctness of the adjugate ratios. -/
private lemma twistedTpPsi_injective (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) :
    Function.Injective (twistedTpPsi (N := N) p hp hpN) := by
  intro j₁ j₂ heq
  by_contra hne
  simp only [twistedTpPsi] at heq
  by_cases h₁ : j₁.val < p <;> by_cases h₂ : j₂.val < p
  · simp only [h₁, h₂, dite_true] at heq
    exact HeckeRing.GL2.adj_upper_inv_mul_not_mem_H p hp j₁.val j₂.val h₁ h₂
      (fun h => hne (Fin.ext h))
      (Gamma0_pair_H_le_GL_pair_H N (adj_inv_mul_mem_H_of_factorisations
        (HeckeCoset.rep (D_p_Gamma0 N p hp.pos)) _ _
        (adj_T_p_upper_factorisation (N := N) p hp hpN j₁.val)
        (adj_T_p_upper_factorisation (N := N) p hp hpN j₂.val) heq))
  · simp only [h₁, dite_true, h₂, dite_false] at heq
    exact HeckeRing.GL2.adj_upper_inv_mul_lower_not_mem_H p hp j₁.val
      (Gamma0_pair_H_le_GL_pair_H N (adj_inv_mul_mem_H_of_factorisations
        (HeckeCoset.rep (D_p_Gamma0 N p hp.pos)) _ _
        (adj_T_p_upper_factorisation (N := N) p hp hpN j₁.val)
        (adj_T_p_lower_factorisation (N := N) p hp hpN) heq))
  · simp only [h₁, dite_false, h₂, dite_true] at heq
    exact HeckeRing.GL2.adj_lower_inv_mul_upper_not_mem_H p hp j₂.val
      (Gamma0_pair_H_le_GL_pair_H N (adj_inv_mul_mem_H_of_factorisations
        (HeckeCoset.rep (D_p_Gamma0 N p hp.pos)) _ _
        (adj_T_p_lower_factorisation (N := N) p hp hpN)
        (adj_T_p_upper_factorisation (N := N) p hp hpN j₂.val) heq))
  · have := j₁.isLt; have := j₂.isLt; omega

/-- The index map `twistedTpPsi` is bijective (injective into a set of matching cardinality
`p + 1 = deg D`). -/
private lemma twistedTpPsi_bijective (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) :
    Function.Bijective (twistedTpPsi (N := N) p hp hpN) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨twistedTpPsi_injective p hp hpN, ?_⟩
  rw [Fintype.card_fin]
  have h := HeckeCoset_deg_D_p_Gamma0 N p hp hpN
  rw [Nat.card_eq_fintype_card] at h; rw [h]

/-- Per-index weighted-value equality: the classical `T_p` summand (upper carries weight
`χ(p)⁻¹`, lower weight `1`) equals the `δ₀`-weighted `tRep_gen` summand at `twistedTpPsi j`. -/
private lemma twistedTpPsi_val_eq (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    {f : ℍ → ℂ} (hf : IsGamma0TwistedInvariant (N := N) k χ f) (j : Fin (p + 1)) :
    (if _h : j.val < p then
      (↑(χ (ZMod.unitOfCoprime p hpN)) : ℂ)⁻¹ • (f ∣[k] (T_p_upper p hp.pos j.val : GL _ ℚ))
    else
      f ∣[k] (T_p_lower p hp.pos : GL _ ℚ)) =
    ((↑(delta0NebentypusWeight (N := N) χ (D_p_Gamma0 N p hp.pos)
        (twistedTpPsi (N := N) p hp hpN j)) : ℂ)⁻¹) •
      (f ∣[k] tRep_gen (Gamma0_pair N) (D_p_Gamma0 N p hp.pos)
        (twistedTpPsi (N := N) p hp hpN j)) := by
  simp only [twistedTpPsi]
  split_ifs with h
  · set e := adj_T_p_upper_factorisation (N := N) p hp hpN j.val with he
    have hval := weighted_value_eq p hp (χ := χ) hf
      (T_p_upper p hp.pos j.val) (adjUpperΔ (N := N) p hp hpN j.val)
      e.choose e.choose_spec.choose
      e.choose_spec.choose_spec.choose
      e.choose_spec.choose_spec.choose_spec.choose
      e.choose_spec.choose_spec.choose_spec.choose_spec rfl
    rw [adjUpperΔ_weight (χ := χ) p hp hpN j.val] at hval
    exact hval
  · set e := adj_T_p_lower_factorisation (N := N) p hp hpN with he
    have hval := weighted_value_eq p hp (χ := χ) hf
      (T_p_lower p hp.pos) (adjLowerΔ (N := N) p hp)
      e.choose e.choose_spec.choose
      e.choose_spec.choose_spec.choose
      e.choose_spec.choose_spec.choose_spec.choose
      e.choose_spec.choose_spec.choose_spec.choose_spec rfl
    rw [adjLowerΔ_weight (χ := χ) p hp, Units.val_one, inv_one, one_smul] at hval
    exact hval

set_option maxHeartbeats 6400000 in
/-- **Twisted matching theorem.** For a `Γ₀(N),χ`-twisted-invariant function `f`, the
abstract χ-weighted Hecke slash `twistedHeckeSlash_gen` at the prime double coset
`D_p_Gamma0` equals the χ-weighted explicit `T_p` coset-sum: each upper representative
`T_p_upper(b)` carries weight `χ(p)⁻¹`, and the lower representative `T_p_lower` carries
weight `1`. This is the twisted analogue of `tRep_gen_D_p_Gamma0_matches_T_p_reps`. -/
theorem twisted_matches_T_p (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) {f : ℍ → ℂ}
    (hf : IsGamma0TwistedInvariant (N := N) k χ f) :
    twistedHeckeSlash_gen (N := N) k χ (D_p_Gamma0 N p hp.pos) f =
      (↑(χ (ZMod.unitOfCoprime p hpN)) : ℂ)⁻¹ •
          (∑ b ∈ Finset.range p, f ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) +
        f ∣[k] (T_p_lower p hp.pos : GL (Fin 2) ℚ) := by
  -- The index permutation `twistedTpPsi`, its per-index weighted-value equality, and its
  -- bijectivity are isolated above (`twistedTpPsi_val_eq`/`twistedTpPsi_bijective`).
  have h_val := twistedTpPsi_val_eq (N := N) (k := k) (χ := χ) p hp hpN hf
  have h_bij := twistedTpPsi_bijective (N := N) p hp hpN
  -- Assemble: rewrite the explicit weighted T_p sum over `Fin (p+1)` and transport via `ψ`.
  rw [twistedHeckeSlash_gen]
  symm
  rw [Finset.smul_sum, ← Fin.sum_univ_eq_sum_range]
  rw [show (∑ j : Fin p, (↑(χ (ZMod.unitOfCoprime p hpN)) : ℂ)⁻¹ •
        (f ∣[k] (T_p_upper p hp.pos j.val : GL _ ℚ))) +
      f ∣[k] (T_p_lower p hp.pos : GL _ ℚ) =
    ∑ j : Fin (p + 1),
      if h : j.val < p then (↑(χ (ZMod.unitOfCoprime p hpN)) : ℂ)⁻¹ •
        (f ∣[k] (T_p_upper p hp.pos j.val : GL _ ℚ))
      else f ∣[k] (T_p_lower p hp.pos : GL _ ℚ) from by
    rw [Fin.sum_univ_castSucc]; congr 1
    · congr 1; ext j; simp [j.isLt]
    · simp]
  rw [Finset.sum_congr rfl (fun j _ => h_val j)]
  exact h_bij.sum_comp
    (fun i => (↑(delta0NebentypusWeight (N := N) χ (D_p_Gamma0 N p hp.pos) i) : ℂ)⁻¹ •
      (f ∣[k] tRep_gen (Gamma0_pair N) (D_p_Gamma0 N p hp.pos) i))

/-- The concrete operator `heckeT_p_all`, applied to a `χ`-eigenform and read as a function,
equals the χ-weighted explicit `T_p` coset sum with the **classical** normalization: the upper
sum carries weight `1` and the lower term carries the diamond `χ(p)`. -/
private lemma heckeT_p_all_coe_eq (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) (hf : f ∈ modFormCharSpace k χ) :
    (⇑(heckeT_p_all k p hp f) : ℍ → ℂ) =
      (∑ b ∈ Finset.range p, (⇑f) ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) +
        (↑(χ (ZMod.unitOfCoprime p hpN)) : ℂ) •
          ((⇑f) ∣[k] (T_p_lower p hp.pos : GL (Fin 2) ℚ)) := by
  -- `heckeT_p_all = heckeT_p` (coprime), whose coercion is `heckeT_p_fun`.
  rw [heckeT_p_all_coprime k hp hpN]
  show heckeT_p_fun k p hp hpN f = _
  rw [heckeT_p_fun, heckeT_p_ut]
  -- On the χ-space, `⟨p⟩ f = χ(p) • f`.
  have hdiam : diamondOp k (ZMod.unitOfCoprime p hpN) f =
      (↑(χ (ZMod.unitOfCoprime p hpN)) : ℂ) • f :=
    (mem_modFormCharSpace_iff k χ f).mp hf (ZMod.unitOfCoprime p hpN)
  rw [show (⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f) : ℍ → ℂ) =
      (↑(χ (ZMod.unitOfCoprime p hpN)) : ℂ) • (⇑f : ℍ → ℂ) from by rw [hdiam]; rfl]
  -- Pull the scalar through the (positive-determinant) slash.
  rw [smul_slash_pos_det k _ _ _ (T_p_lower_det_pos p hp.pos)]

/-- **The normalization bridge.**

For a good prime `p ∤ N` and `f ∈ modFormCharSpace k χ`, the canonical χ-twisted
operator at the prime double coset equals `χ(p)⁻¹` times the concrete operator
`heckeT_p_all`, as functions on `ℍ`:
`heckeRingHomCharSpace (T_single D_p_Gamma0 1) f  =  χ(p)⁻¹ • heckeT_p_all k p hp (↑f)`.

The two sides are χ-weighted sums over the same prime double coset; the gap is the single
scalar `χ(p)⁻¹`, arising because the twisted `δ₀`-weight normalizes by `χ(upper-left of
adj(rep)) = χ(p)` on each of the `p` upper representatives (and `χ(1)=1` on the lower one),
whereas the classical Diamond–Shurman `heckeT_p_all` places the diamond `⟨p⟩ = χ(p)` on the
single lower representative `[[p,0],[0,1]]` instead. -/
theorem heckeRingHomCharSpace_D_p_eq_heckeT_p_all (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N)
    (f : modFormCharSpace k χ) :
    (⇑((heckeRingHomCharSpace (k := k) (χ := χ) (T_single (Gamma0_pair N) ℤ
        (D_p_Gamma0 N p hp.pos) 1) f : modFormCharSpace k χ) :
        ModularForm ((Gamma1 N).map (mapGL ℝ)) k) : ℍ → ℂ) =
      (↑(χ (ZMod.unitOfCoprime p hpN)) : ℂ)⁻¹ •
        (⇑(heckeT_p_all k p hp (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)) : ℍ → ℂ) := by
  -- LHS: unfold `heckeRingHomCharSpace` at a single coset to `twistedHeckeSlash_gen`.
  have hLHS : (⇑((heckeRingHomCharSpace (k := k) (χ := χ) (T_single (Gamma0_pair N) ℤ
      (D_p_Gamma0 N p hp.pos) 1) f : modFormCharSpace k χ) :
      ModularForm ((Gamma1 N).map (mapGL ℝ)) k) : ℍ → ℂ) =
        twistedHeckeSlash_gen (N := N) k χ (D_p_Gamma0 N p hp.pos)
          (⇑(f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)) := by
    change (⇑(((nebentypusHeckeSum (N := N) (k := k) (χ := χ)
        (T_single (Gamma0_pair N) ℤ (D_p_Gamma0 N p hp.pos) 1)) f :
        modFormCharSpace k χ) : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) : ℍ → ℂ) = _
    rw [nebentypusHeckeSum_apply_coe, twistedHeckeSlashExt_gen]
    rw [Finsupp.sum_single_index (by simp :
      (0 : ℤ) • twistedHeckeSlash_gen (N := N) k χ (D_p_Gamma0 N p hp.pos)
        (⇑(f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)) = 0)]
    rw [one_smul]
  rw [hLHS]
  -- Apply the twisted matching theorem.
  rw [twisted_matches_T_p (k := k) (χ := χ) p hp hpN
    (coe_mem_twistedInvariant (f : ModularForm _ k) f.2)]
  -- Rewrite the concrete operator's function.
  rw [heckeT_p_all_coe_eq (k := k) (χ := χ) p hp hpN
    (f : ModularForm _ k) f.2]
  -- Both sides are now explicit; match by distributing `χ(p)⁻¹`.
  rw [smul_add, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul]

/-! ### The scalar/diamond coset `T(p,p)` (good prime `p ∤ N`)

The double coset `T_diag_Gamma0 N ![p,p]` (image of `X_(p,1)` under `ψ_hom` for `p ∤ N`)
has the single central representative `diag(p,p) = p·I`.  Slashing a weight-`k` form by
`diag(p,p)` multiplies it by `p^(k-2)`; the twisted `δ₀`-weight at the (unique) coset
normalizes by `χ(p)`.  Hence the operator at `T(p,p)` is the scalar `χ(p)⁻¹·p^(k-2)`. -/

/-- **Slash by the central scalar `diag(c,c)`.** For `c > 0` a natural number, the weight-`k`
slash by `diagMat 2 (fun _ => c)` multiplies a function by `c^(k-2)`: the Möbius action is
trivial, `denom = c`, `det = c²` and `σ = id` (positive determinant). -/
private lemma slash_diag_scalar (k : ℤ) (c : ℕ) (hc : 0 < c) (f : ℍ → ℂ) :
    f ∣[k] (diagMat 2 (fun _ : Fin 2 => c) : GL (Fin 2) ℚ) = (c : ℂ) ^ (k - 2) • f := by
  have hcpos : ∀ i : Fin 2, 0 < (fun _ : Fin 2 => c) i := fun _ => hc
  have hcQ : (0 : ℚ) < (c : ℚ) := by exact_mod_cast hc
  -- Determinant of `diag(c,c)` is `c² > 0`.
  have hdetpos : 0 < (diagMat 2 (fun _ : Fin 2 => c) : GL (Fin 2) ℚ).det.val := by
    rw [GeneralLinearGroup.val_det_apply, diagMat_val _ _ hcpos, Matrix.det_diagonal,
      Fin.prod_univ_two]
    positivity
  -- `σ (glMap (diag c c)) = id` since the determinant is positive.
  have hσ : UpperHalfPlane.σ (glMap (diagMat 2 (fun _ : Fin 2 => c) : GL (Fin 2) ℚ)) =
      RingHom.id ℂ := by
    unfold UpperHalfPlane.σ
    simp only [glMap_det_pos_of_rat_det_pos _ hdetpos, ↓reduceIte]
  have hcne : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hc.ne'
  ext z
  show (f ∣[k] glMap (diagMat 2 (fun _ : Fin 2 => c) : GL (Fin 2) ℚ)) z = ((c : ℂ) ^ (k - 2) • f) z
  rw [ModularForm.slash_apply, hσ]
  -- The Möbius action of the scalar matrix `diag(c,c)` is the identity on `ℍ`.
  have hsmul : (glMap (diagMat 2 (fun _ : Fin 2 => c) : GL (Fin 2) ℚ)) • z = z := by
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_smul_of_det_pos (glMap_det_pos_of_rat_det_pos _ hdetpos)]
    show ((glMap (diagMat 2 (fun _ : Fin 2 => c) : GL (Fin 2) ℚ)) 0 0 * (z : ℂ) +
        (glMap (diagMat 2 (fun _ : Fin 2 => c) : GL (Fin 2) ℚ)) 0 1) /
        ((glMap (diagMat 2 (fun _ : Fin 2 => c) : GL (Fin 2) ℚ)) 1 0 * (z : ℂ) +
          (glMap (diagMat 2 (fun _ : Fin 2 => c) : GL (Fin 2) ℚ)) 1 1) = (z : ℂ)
    simp [glMap, GeneralLinearGroup.map, diagMat_val _ _ hcpos, Matrix.map_apply]
    field_simp
  -- `denom (glMap (diag c c)) z = c`.
  have hdenom : UpperHalfPlane.denom (glMap (diagMat 2 (fun _ : Fin 2 => c) : GL (Fin 2) ℚ)) z =
      (c : ℂ) := by
    show (glMap (diagMat 2 (fun _ : Fin 2 => c) : GL (Fin 2) ℚ)) 1 0 * (z : ℂ) +
        (glMap (diagMat 2 (fun _ : Fin 2 => c) : GL (Fin 2) ℚ)) 1 1 = (c : ℂ)
    simp [glMap, GeneralLinearGroup.map, diagMat_val _ _ hcpos, Matrix.map_apply]
  -- `|det| = c²`.
  have habsdet : (↑|(glMap (diagMat 2 (fun _ : Fin 2 => c) : GL (Fin 2) ℚ)).det.val| : ℂ) =
      (c : ℂ) ^ 2 := by
    have hdet : (glMap (diagMat 2 (fun _ : Fin 2 => c) : GL (Fin 2) ℚ)).det.val =
        algebraMap ℚ ℝ (diagMat 2 (fun _ : Fin 2 => c) : GL (Fin 2) ℚ).det.val :=
      congr_arg Units.val (GeneralLinearGroup.map_det (algebraMap ℚ ℝ) _)
    rw [hdet, GeneralLinearGroup.val_det_apply, diagMat_val _ _ hcpos, Matrix.det_diagonal,
      Fin.prod_univ_two]
    simp only [map_mul, map_natCast]
    rw [abs_of_nonneg (by positivity)]; push_cast; ring
  rw [hsmul, hdenom, habsdet, RingHom.id_apply]
  -- `f z · (c²)^(k-1) · c^(-k) = c^(k-2) · f z`.
  show f z * ((c : ℂ) ^ 2) ^ (k - 1) * (c : ℂ) ^ (-k) = (c : ℂ) ^ (k - 2) * f z
  rw [show ((c : ℂ) ^ 2) = (c : ℂ) ^ (2 : ℤ) from by norm_cast, ← zpow_mul, mul_assoc,
    ← zpow_add₀ hcne, mul_comm]
  congr 1; ring_nf

/-- The scalar double coset `T_diag_Gamma0 N ![c,c]` (the image of `X_(c,1)`) is a single
left `Γ₀(N)`-coset, because `diag(c,c) = c·I` centralizes `Γ₀(N)`. Reconstruction of the
private `Gamma0_HeckeCoset_deg_scalar` (degree-1 conclusion) via the public scalar-conjugation
lemmas. -/
private lemma subsingleton_decompQuot_scalar (c : ℕ) (hc : 0 < c)
    (hgcd : Int.gcd (c : ℤ) (N : ℤ) = 1) :
    Subsingleton (decompQuot (Gamma0_pair N)
      (HeckeCoset.rep (T_diag_Gamma0 N (fun _ : Fin 2 => c) (fun _ => hc) hgcd))) := by
  set D := T_diag_Gamma0 N (fun _ : Fin 2 => c) (fun _ => hc) hgcd with hD
  set δ := HeckeCoset.rep D with hδ
  set H := (Gamma0_pair N).H with hH
  -- The degree of `D` is 1: `ConjAct (δ) • H = H` because `δ` is `(scalar)·(H-element)`.
  suffices hcard : Fintype.card (decompQuot (Gamma0_pair N) δ) = 1 from
    Fintype.card_le_one_iff_subsingleton.mp (le_of_eq hcard)
  suffices hsmul : ConjAct.toConjAct (δ : GL (Fin 2) ℚ) • H = H by
    have h_def : (Fintype.card (decompQuot (Gamma0_pair N) δ) : ℤ) =
        ↑((ConjAct.toConjAct (δ : GL (Fin 2) ℚ) • H).relIndex H) := by
      simp only [Subgroup.relIndex, Subgroup.index, ← Nat.card_eq_fintype_card]; rfl
    have : (Fintype.card (decompQuot (Gamma0_pair N) δ) : ℤ) = 1 := by
      rw [h_def, hsmul, Subgroup.relIndex_self]; simp
    exact_mod_cast this
  -- `δ ∈ DC(diag(c,c))`, so `δ = (h₁·h₂)·diag(c,c)` and conjugation by `δ` fixes `H`.
  have hδ_mem : (δ : GL (Fin 2) ℚ) ∈
      DoubleCoset.doubleCoset (diagMat 2 (fun _ : Fin 2 => c) : GL (Fin 2) ℚ) H H := by
    have h1 : HeckeCoset.toSet D =
        DoubleCoset.doubleCoset (diagMat 2 (fun _ : Fin 2 => c) : GL (Fin 2) ℚ) H H := by
      simp only [hD, T_diag_Gamma0, HeckeCoset.toSet_mk]; rfl
    rw [← h1]; exact HeckeCoset.rep_mem D
  rw [DoubleCoset.mem_doubleCoset] at hδ_mem
  obtain ⟨h₁, hh₁, h₂, hh₂, hδ_eq⟩ := hδ_mem
  have hδ_simp : (δ : GL (Fin 2) ℚ) = (h₁ * h₂) * diagMat 2 (fun _ : Fin 2 => c) := by
    rw [hδ_eq, mul_assoc, diagMat_scalar_comm 2 c hc h₂, ← mul_assoc]
  rw [hδ_simp, map_mul, ← smul_smul]
  -- Conjugation by the scalar fixes `H` (entrywise), then conjugation by `h₁·h₂ ∈ H` fixes `H`.
  have hscalar_smul : ConjAct.toConjAct (diagMat 2 (fun _ : Fin 2 => c)) • H = H := by
    ext x
    simp only [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def,
      map_inv, ConjAct.ofConjAct_toConjAct, inv_inv]
    rw [diagMat_scalar_conj_eq 2 c hc]
  rw [hscalar_smul]
  ext x
  simp only [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def,
    map_inv, ConjAct.ofConjAct_toConjAct, inv_inv]
  constructor
  · intro hx
    have hxe : x = (h₁ * h₂) * ((h₁ * h₂)⁻¹ * x * (h₁ * h₂)) * (h₁ * h₂)⁻¹ := by group
    rw [hxe]
    exact H.mul_mem (H.mul_mem (H.mul_mem hh₁ hh₂) hx) (H.inv_mem (H.mul_mem hh₁ hh₂))
  · intro hx
    exact H.mul_mem (H.mul_mem (H.inv_mem (H.mul_mem hh₁ hh₂)) hx) (H.mul_mem hh₁ hh₂)

/-- The adjugate of the central scalar `diag(c,c)` is itself. -/
private lemma adj_diag_scalar (c : ℕ) (hc : 0 < c) :
    GL_adjugate (diagMat 2 (fun _ : Fin 2 => c) : GL (Fin 2) ℚ) =
      (diagMat 2 (fun _ : Fin 2 => c) : GL (Fin 2) ℚ) := by
  have hcpos : ∀ i : Fin 2, 0 < (fun _ : Fin 2 => c) i := fun _ => hc
  apply Units.ext; ext i j
  rw [GL_adjugate_val, diagMat_val _ _ hcpos, Matrix.adjugate_fin_two]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal, Matrix.of_apply]

omit [NeZero N] in
/-- `diag(c,c)` lies in `Δ₀(N)` for `gcd(c,N) = 1`. (Mirror of `diag_1p_mem_Delta0`, with
the `gcd` hypothesis carrying the upper-left entry `c`.) -/
private lemma diag_scalar_mem_Delta0 (c : ℕ) (hc : 0 < c)
    (hgcd : Int.gcd (c : ℤ) (N : ℤ) = 1) :
    (diagMat 2 (fun _ : Fin 2 => c) : GL (Fin 2) ℚ) ∈ Delta0_submonoid N := by
  have hcpos : ∀ i : Fin 2, 0 < (fun _ : Fin 2 => c) i := fun _ => hc
  set A : Matrix (Fin 2) (Fin 2) ℤ := Matrix.diagonal (fun _ : Fin 2 => (c : ℤ)) with hA
  have hA_eq : (↑(diagMat 2 (fun _ : Fin 2 => c)) : Matrix _ _ ℚ) = A.map (Int.cast : ℤ → ℚ) := by
    rw [diagMat_val _ _ hcpos]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [A, Matrix.diagonal, Matrix.map_apply]
  have hcQ : (0 : ℚ) < (c : ℚ) := by exact_mod_cast hc
  refine ⟨⟨A, hA_eq⟩, ?_, A, hA_eq, ?_, ?_⟩
  · rw [diagMat_val _ _ hcpos, Matrix.det_diagonal, Fin.prod_univ_two]
    positivity
  · simp [A, Matrix.diagonal]
  · simpa [A, Matrix.diagonal] using hgcd

/-- `diag(c,c)` (with `gcd(c,N)=1`) as an element of `Δ₀(N)`, its upper-left integral
witness being `c`, so its `δ₀`-character is `χ(c mod N)`. -/
private noncomputable def diagScalarΔ (c : ℕ) (hc : 0 < c)
    (hgcd : Int.gcd (c : ℤ) (N : ℤ) = 1) : (Gamma0_pair N).Δ :=
  ⟨diagMat 2 (fun _ : Fin 2 => c), diag_scalar_mem_Delta0 (N := N) c hc hgcd⟩

@[simp] private lemma diagScalarΔ_coe (c : ℕ) (hc : 0 < c)
    (hgcd : Int.gcd (c : ℤ) (N : ℤ) = 1) :
    (diagScalarΔ (N := N) c hc hgcd : GL (Fin 2) ℚ) =
      diagMat 2 (fun _ : Fin 2 => c) := rfl

/-- The `δ₀`-weight at the scalar `diag(c,c)`: `δ₀(diag(c,c)) = χ(c mod N)`. -/
private lemma diagScalarΔ_weight (χ : (ZMod N)ˣ →* ℂˣ) (c : ℕ) (hc : 0 < c)
    (hgcd : Int.gcd (c : ℤ) (N : ℤ) = 1) (hcop : Nat.Coprime c N) :
    delta0NebentypusDeltaChar (N := N) χ (diagScalarΔ (N := N) c hc hgcd) =
      χ (ZMod.unitOfCoprime c hcop) := by
  have hcpos : ∀ i : Fin 2, 0 < (fun _ : Fin 2 => c) i := fun _ => hc
  unfold delta0NebentypusDeltaChar
  simp only [MonoidHom.coe_mk, OneHom.coe_mk]
  congr 1
  apply Units.ext
  rw [Delta0UpperUnit_val, ZMod.coe_unitOfCoprime]
  -- The integer witness of `diag(c,c)` is `diagonal ![c,c]`, upper-left `c`.
  have hwit : delta0IntegralMatrix (N := N) (diagScalarΔ (N := N) c hc hgcd) =
      Matrix.diagonal (fun _ : Fin 2 => (c : ℤ)) := by
    apply delta0IntegralMatrix_witness_unique
    rw [diagScalarΔ_coe, diagMat_val _ _ hcpos]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, Matrix.map_apply]
  rw [hwit]; simp [Matrix.diagonal]

/-- Adjugate factorisation of the central scalar `diag(p,p)` through the scalar double-coset
representative: `adj(diag(p,p)) = diag(p,p) = h₁ · rep · h₂` with `h₁,h₂ ∈ Γ₀(N)`. -/
private lemma adj_diagScalar_factorisation (p : ℕ) (hp : Nat.Prime p)
    (hgcd : Int.gcd (p : ℤ) (N : ℤ) = 1) :
    ∃ (h₁ : GL (Fin 2) ℚ) (_ : h₁ ∈ (Gamma0_pair N).H)
      (h₂ : GL (Fin 2) ℚ) (_ : h₂ ∈ (Gamma0_pair N).H),
      GL_adjugate (diagMat 2 (fun _ : Fin 2 => p) : GL (Fin 2) ℚ) =
        h₁ * (HeckeCoset.rep (T_diag_Gamma0 N (fun _ : Fin 2 => p) (fun _ => hp.pos) hgcd)
          : GL _ ℚ) * h₂ := by
  set D := T_diag_Gamma0 N (fun _ : Fin 2 => p) (fun _ => hp.pos) hgcd with hD
  -- `rep D ∈ DC(diag(p,p))`, so `rep = a · diag(p,p) · c` with `a, c ∈ H`.
  have hrep := HeckeCoset.rep_mem D
  rw [hD, T_diag_Gamma0, HeckeCoset.toSet_mk, DoubleCoset.mem_doubleCoset] at hrep
  obtain ⟨a, ha, c, hc, hrep_eq⟩ := hrep
  -- So `diag(p,p) = a⁻¹ · rep · c⁻¹`, and `adj(diag(p,p)) = diag(p,p)`.
  refine ⟨a⁻¹, (Gamma0_pair N).H.inv_mem ha, c⁻¹, (Gamma0_pair N).H.inv_mem hc, ?_⟩
  rw [adj_diag_scalar p hp.pos]
  rw [show (HeckeCoset.rep D : GL _ ℚ) =
    a * (diagMat 2 (fun _ : Fin 2 => p) : GL _ ℚ) * c from hrep_eq]
  group

/-- The `δ₀`-weight of the scalar triple `gamma0TripleDelta D h₁ h₂` (with `D` the scalar
double coset and `h₁·rep·h₂ = adj(diag(p,p)) = diag(p,p)`) equals `χ(p mod N)`. -/
private lemma diagScalar_triple_weight (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (hgcd : Int.gcd (p : ℤ) (N : ℤ) = 1)
    (h₁ : GL (Fin 2) ℚ) (hh₁ : h₁ ∈ (Gamma0_pair N).H)
    (h₂ : GL (Fin 2) ℚ) (hh₂ : h₂ ∈ (Gamma0_pair N).H)
    (hfact : GL_adjugate (diagMat 2 (fun _ : Fin 2 => p) : GL (Fin 2) ℚ) =
      h₁ * (HeckeCoset.rep (T_diag_Gamma0 N (fun _ : Fin 2 => p) (fun _ => hp.pos) hgcd)
        : GL _ ℚ) * h₂) :
    delta0NebentypusDeltaChar (N := N) χ
      (gamma0TripleDelta (N := N)
        (T_diag_Gamma0 N (fun _ : Fin 2 => p) (fun _ => hp.pos) hgcd) h₁ hh₁ h₂ hh₂) =
      χ (ZMod.unitOfCoprime p hpN) := by
  rw [← diagScalarΔ_weight (N := N) χ p hp.pos hgcd hpN]
  apply delta0Char_congr
  -- Both `Δ`-elements have matrix `h₁·rep·h₂ = adj(diag(p,p)) = diag(p,p)`.
  change h₁ * (HeckeCoset.rep (T_diag_Gamma0 N (fun _ : Fin 2 => p) (fun _ => hp.pos) hgcd)
      : GL _ ℚ) * h₂ = diagMat 2 (fun _ : Fin 2 => p)
  rw [← hfact, adj_diag_scalar p hp.pos]

set_option maxHeartbeats 1600000 in
/-- **The scalar/diamond coset `T(p,p)`, good prime `p ∤ N`.**

For `p ∤ N` and `f ∈ modFormCharSpace k χ`, the operator at the scalar double coset
`T_diag_Gamma0 N ![p,p]` (image of `X_(p,1)` under `ψ_hom`) acts as the scalar
`χ(p)⁻¹ · p^(k-2)`:
`heckeRingHomCharSpace (T_single (T_diag_Gamma0 N ![p,p]) 1) f = (χ(p)⁻¹ · p^(k-2)) • f`.

The single central representative `diag(p,p)` slashes a weight-`k` form by `p^(k-2)`
(`slash_diag_scalar`); the twisted `δ₀`-weight normalizes by `χ(p)`
(`diagScalarΔ_weight`). Equivalently, since `⟨p⟩f = χ(p)·f` on the χ-space, this is
`p^(k-2) • (diamondOp k ⟨p⟩⁻¹ f)`. -/
theorem heckeRingHomCharSpace_T_pp_eq_scalar (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N)
    (f : modFormCharSpace k χ) :
    (⇑((heckeRingHomCharSpace (k := k) (χ := χ) (T_single (Gamma0_pair N) ℤ
        (T_diag_Gamma0 N (fun _ : Fin 2 => p) (fun _ => hp.pos)
          (by rw [Int.gcd_natCast_natCast]; exact hpN)) 1) f : modFormCharSpace k χ) :
        ModularForm ((Gamma1 N).map (mapGL ℝ)) k) : ℍ → ℂ) =
      ((↑(χ (ZMod.unitOfCoprime p hpN)) : ℂ)⁻¹ * (p : ℂ) ^ (k - 2)) •
        (⇑(f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) : ℍ → ℂ) := by
  classical
  have hgcd : Int.gcd (p : ℤ) (N : ℤ) = 1 := by rw [Int.gcd_natCast_natCast]; exact hpN
  set D := T_diag_Gamma0 N (fun _ : Fin 2 => p) (fun _ => hp.pos) hgcd with hD
  set f0 : ModularForm ((Gamma1 N).map (mapGL ℝ)) k :=
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) with hf0
  have hf0mem : f0 ∈ modFormCharSpace k χ := f.2
  have hf0inv : IsGamma0TwistedInvariant (N := N) k χ (⇑f0) :=
    coe_mem_twistedInvariant f0 hf0mem
  -- LHS: unfold `heckeRingHomCharSpace` at a single coset to `twistedHeckeSlash_gen`.
  have hLHS : (⇑((heckeRingHomCharSpace (k := k) (χ := χ) (T_single (Gamma0_pair N) ℤ D 1) f :
      modFormCharSpace k χ) : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) : ℍ → ℂ) =
        twistedHeckeSlash_gen (N := N) k χ D (⇑f0) := by
    change (⇑(((nebentypusHeckeSum (N := N) (k := k) (χ := χ)
        (T_single (Gamma0_pair N) ℤ D 1)) f :
        modFormCharSpace k χ) : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) : ℍ → ℂ) = _
    rw [nebentypusHeckeSum_apply_coe, twistedHeckeSlashExt_gen]
    rw [Finsupp.sum_single_index (by simp :
      (0 : ℤ) • twistedHeckeSlash_gen (N := N) k χ D (⇑f0) = 0)]
    rw [one_smul]
  rw [hLHS]
  -- `decompQuot` for `D` is a singleton.
  haveI hsub : Subsingleton (decompQuot (Gamma0_pair N) (HeckeCoset.rep D)) :=
    subsingleton_decompQuot_scalar (N := N) p hp.pos hgcd
  -- Factorise `adj(diag(p,p)) = h₁ · rep · h₂` (isolated as `adj_diagScalar_factorisation`).
  obtain ⟨h₁, hh₁, h₂, hh₂, hfact⟩ := adj_diagScalar_factorisation (N := N) p hp hgcd
  rw [← hD] at hfact
  -- The unique index of the decomposition.
  set q : decompQuot (Gamma0_pair N) (HeckeCoset.rep D) := ⟦⟨h₁, hh₁⟩⟧ with hq
  -- The single summand of `twistedHeckeSlash_gen` equals the weighted slash by `diag(p,p)`.
  rw [twistedHeckeSlash_gen, Fintype.sum_subsingleton _ q]
  -- Apply the twisted matching of the factorisation.
  have hmatch := twisted_weighted_slash_tRep_gen_of_mem (N := N) k χ D h₁ hh₁ h₂ hh₂ (⇑f0) hf0inv
  simp only [hq] at hmatch ⊢
  -- RHS of `hmatch` is the summand at `q` (the `delta0NebentypusWeight` is the same `δ₀`).
  rw [show delta0NebentypusWeight (N := N) χ D ⟦(⟨h₁, hh₁⟩ : (Gamma0_pair N).H)⟧ =
    delta0NebentypusDeltaChar (N := N) χ (deltaRep_gen (N := N) D ⟦⟨h₁, hh₁⟩⟧) from rfl,
    ← hmatch]
  -- `adj(h₁·rep·h₂) = adj(adj(diag(p,p))) = diag(p,p)`.
  rw [← hfact, GL_adjugate_involutive]
  -- The `δ₀`-weight on the triple equals `δ₀(diag(p,p)) = χ(p)` (`diagScalar_triple_weight`).
  have hwgt := diagScalar_triple_weight (N := N) (χ := χ) p hp hpN hgcd
    h₁ hh₁ h₂ hh₂ (hD ▸ hfact)
  rw [← hD] at hwgt
  rw [hwgt, slash_diag_scalar k p hp.pos (⇑f0), smul_smul]

/-! ### The bad-prime obstruction: `U_p`, `p ∣ N`

For `p ∣ N`, the project's `U_p` is `heckeT_p_divN k p`, whose coercion is the upper-triangular
sum `∑_{b<p} f ∣[k] T_p_upper(b)` (no lower term, no diamond — DS 5.2.2 / 5.5.2).  The
candidate bad-prime double coset is `D_p_Gamma0 N p` (= `T_diag_Gamma0 N ![1,p]`, the image
of `X_(p,0)` under `ψ_hom`; `T(p,p) = X_(p,1) ↦ 0` for `p ∣ N`).

**The good-prime bridge does not transfer.** The twisted `twistedHeckeSlash_gen` slashes by the
*adjugated* representatives `tRep_gen = adj(σᵢ·rep)`, and the matching theorem
`twisted_matches_T_p` works only because, for `p ∤ N`, the double coset is stable under
adjugation (`adj_rep_mem`, which needs `Nat.Coprime p N`).  For `p ∣ N` this fails: the
adjugate `adj(T_p_upper b) = !![p, -b; 0, 1]` has top-left entry `p`, which is *not* coprime to
`N`, so it escapes `Δ₀(N)` (and hence `D_p_Gamma0`).  This is the same phenomenon recorded in
`BadPrimeDoubleCoset.lean`: the bad-prime upper reps `T_p_upper b` and the lower-offset
reps `!![p,0;-N·b,1]` are conjugate only via the **Atkin–Lehner** involution `W_N`, not via
`Γ₀(N)`/`Γ₁(N)`.  Consequently the operator at `D_p_Gamma0` (`p ∣ N`) computes the Atkin–Lehner /
adjugate transform of `heckeT_p_divN`, not `heckeT_p_divN` itself; and the would-be scalar
`χ(p)` is not even defined (`p` is a non-unit mod `N`).

The lemma below is the precise matrix-level obstruction. -/

omit [NeZero N] in
/-- **Bad-prime obstruction (matrix level).** For `p ∣ N`, the adjugate of the upper-triangular
representative `T_p_upper p b` — which is the kind of matrix `tRep_gen` slashes by —
does **not** lie in `Δ₀(N)`, because its top-left entry `p` is not coprime to `N`.  Hence it is
not in the double coset `D_p_Gamma0 N p`, so the adjugation-stability argument underlying the
good-prime bridge `twisted_matches_T_p` cannot hold for `p ∣ N`. -/
lemma adj_T_p_upper_not_mem_Delta0_of_dvd (p : ℕ) (hp : Nat.Prime p)
    (hpN : ¬ Nat.Coprime p N) (b : ℕ) :
    GL_adjugate (T_p_upper p hp.pos b : GL (Fin 2) ℚ) ∉ Delta0_submonoid N := by
  intro hmem
  obtain ⟨_, _, A, hA, _, hAco⟩ := hmem
  -- The integral witness `A` satisfies `A.map cast = adj(T_p_upper b) = !![p,-b;0,1]`,
  -- so `A 0 0 = p` (cast is injective).
  have hA00 : A 0 0 = (p : ℤ) := by
    have hcast : ((A 0 0 : ℤ) : ℚ) = (p : ℚ) := by
      have := congrFun (congrFun hA 0) 0
      rw [GL_adjugate_val, T_p_upper_coe, Matrix.adjugate_fin_two] at this
      simpa [Matrix.map_apply] using this.symm
    exact_mod_cast hcast
  rw [hA00] at hAco
  -- `gcd(p, N) = 1` contradicts `p ∣ N` (since `p` is prime, `gcd(p,N) = p ≠ 1`).
  exact hpN (by rwa [Int.gcd_natCast_natCast] at hAco)

end Bridge

/-! ## Transporting the level-1 multiplication table to χ-space operators

The composite `heckeRingHomCharSpace ∘ φ`, where `φ : 𝕋 (GL_pair 2) ℤ →+* 𝕋
(Gamma0_pair N) ℤ` is the Shimura 3.35 surjection, is a ring hom from the
*level-1* Hecke algebra `HeckeAlgebra 2 = 𝕋 (GL_pair 2) ℤ` into the χ-space
endomorphism ring `Module.End ℂ (modFormCharSpace k χ)`, and the proven level-1
multiplication identities (`T_sum_mul_coprime`, `T_sum_ppow_recurrence` from
`MultiplicationTable.lean`) push forward to operator identities on the χ-space with no
new combinatorics — just `congrArg` plus `map_mul`/`map_add`/`map_zsmul`.

`HeckeAlgebra 2` is *definitionally* `𝕋 (GL_pair 2) ℤ`, so the level-1 elements
`T_sum`, `T_pp` are already valued in the domain of `φ`. -/
section TableTransport

open HeckeRing.GL2

variable {k : ℤ} {χ : (ZMod N)ˣ →* ℂˣ}

/-- **Schematic transport (the core observation).** The composite of the Shimura 3.35
surjection `φ` with the canonical χ-twisted action `heckeRingHomCharSpace` is a ring
homomorphism from the level-1 Hecke algebra to the χ-space endomorphisms; hence ANY ring
identity `a = b` in `𝕋 (GL_pair 2) ℤ` becomes the operator identity `Φ a = Φ b`, and
products go to compositions: `Φ (a * b) = Φ a * Φ b`. No new combinatorics. -/
theorem heckeRingHomCharSpace_table_transport_schematic
    (φ : 𝕋 (GL_pair 2) ℤ →+* 𝕋 (Gamma0_pair N) ℤ) :
    let Φ : 𝕋 (GL_pair 2) ℤ →+* Module.End ℂ (modFormCharSpace k χ) :=
      (heckeRingHomCharSpace (N := N) (k := k) (χ := χ)).comp φ
    (∀ a b : 𝕋 (GL_pair 2) ℤ, a = b → Φ a = Φ b) ∧
      (∀ a b : 𝕋 (GL_pair 2) ℤ, Φ (a * b) = Φ a * Φ b) ∧
      (∀ a b : 𝕋 (GL_pair 2) ℤ, Φ (a + b) = Φ a + Φ b) := by
  intro Φ
  exact ⟨fun a b h => congrArg Φ h, fun a b => map_mul Φ a b, fun a b => map_add Φ a b⟩

/-- **Coprime-multiplicativity transports to χ-space operators.** For coprime `m, n`,
the level-1 identity `T(m) · T(n) = T(mn)` (`T_sum_mul_coprime`) becomes the operator
identity `Φ(T(m)) ∘ Φ(T(n)) = Φ(T(mn))` on `modFormCharSpace k χ`, where `Φ =
heckeRingHomCharSpace ∘ φ`. Derived purely by `congrArg Φ` on the ring identity followed by
`map_mul` — no χ-level combinatorics is introduced. -/
theorem heckeRingHomCharSpace_table_transports_coprime
    (φ : 𝕋 (GL_pair 2) ℤ →+* 𝕋 (Gamma0_pair N) ℤ)
    (m n : ℕ+) (hcop : Nat.Coprime m n) :
    ((heckeRingHomCharSpace (N := N) (k := k) (χ := χ)).comp φ) (T_sum m) *
        ((heckeRingHomCharSpace (N := N) (k := k) (χ := χ)).comp φ) (T_sum n) =
      ((heckeRingHomCharSpace (N := N) (k := k) (χ := χ)).comp φ)
        (T_sum ⟨m * n, Nat.mul_pos m.pos n.pos⟩) := by
  set Φ := (heckeRingHomCharSpace (N := N) (k := k) (χ := χ)).comp φ with hΦ
  -- Push the level-1 ring identity through the ring hom `Φ`.
  rw [← map_mul Φ (T_sum m) (T_sum n)]
  exact congrArg Φ (T_sum_mul_coprime m n hcop)

/-- **Prime-power recurrence transports to χ-space operators.** For a prime `p` and
`k ≥ 1`, the level-1 recurrence
`T(p^{k+1}) = T(p)·T(p^k) − p·T(p,p)·T(p^{k-1})` (`T_sum_ppow_recurrence`)
becomes the operator identity
`Φ(T(p^{k+1})) = Φ(T(p)) ∘ Φ(T(p^k)) − p · (Φ(T(p,p)) ∘ Φ(T(p^{k-1})))`
on `modFormCharSpace k χ`. Derived by `congrArg Φ` plus `map_mul`/`map_zsmul`. -/
theorem heckeRingHomCharSpace_table_transports_ppow_recurrence
    (φ : 𝕋 (GL_pair 2) ℤ →+* 𝕋 (Gamma0_pair N) ℤ)
    (p : ℕ) (hp : p.Prime) (j : ℕ) (hj : 0 < j) :
    ((heckeRingHomCharSpace (N := N) (k := k) (χ := χ)).comp φ)
        (T_sum ⟨p ^ (j + 1), pow_pos hp.pos (j + 1)⟩) =
      ((heckeRingHomCharSpace (N := N) (k := k) (χ := χ)).comp φ) (T_sum ⟨p, hp.pos⟩) *
          ((heckeRingHomCharSpace (N := N) (k := k) (χ := χ)).comp φ)
            (T_sum ⟨p ^ j, pow_pos hp.pos j⟩) -
        (p : ℤ) • (((heckeRingHomCharSpace (N := N) (k := k) (χ := χ)).comp φ) (T_pp p) *
          ((heckeRingHomCharSpace (N := N) (k := k) (χ := χ)).comp φ)
            (T_sum ⟨p ^ (j - 1), pow_pos hp.pos (j - 1)⟩)) := by
  set Φ := (heckeRingHomCharSpace (N := N) (k := k) (χ := χ)).comp φ with hΦ
  -- Express the RHS as `Φ` applied to the level-1 RHS, then transport the identity.
  rw [← map_mul Φ (T_sum ⟨p, hp.pos⟩) (T_sum ⟨p ^ j, pow_pos hp.pos j⟩),
    ← map_mul Φ (T_pp p) (T_sum ⟨p ^ (j - 1), pow_pos hp.pos (j - 1)⟩),
    ← map_zsmul Φ (p : ℤ) (T_pp p * T_sum ⟨p ^ (j - 1), pow_pos hp.pos (j - 1)⟩),
    ← map_sub Φ]
  exact congrArg Φ (T_sum_ppow_recurrence p hp j hj)

/-- **End-to-end demonstrator.** Obtaining `φ` from Shimura 3.35, the level-1 coprime
identity transports to a genuine *operator* identity on `modFormCharSpace k χ`: there is
a ring hom `Φ` from the level-1 Hecke algebra to the χ-space endomorphisms such that
`Φ(T(m)) ∘ Φ(T(n)) = Φ(T(mn))` for all coprime `m, n`. This packages the whole pipeline
`level-1 table → φ (Shimura 3.35) → heckeRingHomCharSpace (χ-action)`. -/
theorem heckeRingHomCharSpace_table_transports_coprime_via_shimura
    (m n : ℕ+) (hcop : Nat.Coprime m n) :
    ∃ Φ : 𝕋 (GL_pair 2) ℤ →+* Module.End ℂ (modFormCharSpace k χ),
      Φ (T_sum m) * Φ (T_sum n) = Φ (T_sum ⟨m * n, Nat.mul_pos m.pos n.pos⟩) := by
  obtain ⟨φ, _hφ⟩ := shimura_thm_3_35 N
  refine ⟨(heckeRingHomCharSpace (N := N) (k := k) (χ := χ)).comp φ, ?_⟩
  exact heckeRingHomCharSpace_table_transports_coprime (k := k) (χ := χ) φ m n hcop

end TableTransport

/-! ## Operator relations derived from the ring on the χ-space

The concrete Hecke operators' commutativity on the
nebentypus eigenspace `modFormCharSpace k χ` is a *ring corollary*, not a coset
computation. The Γ₀(N) Hecke ring is commutative
(`Gamma0_pair_HeckeAlgebra_mul_comm`), `heckeRingHomCharSpace` is a ring hom into the χ-space
endomorphisms, and the bridge `heckeRingHomCharSpace_D_p_eq_heckeT_p_all` identifies the
canonical operator at the prime double coset `D_p` with `χ(p)⁻¹ · heckeT_p_all` on the
χ-space. Composing these yields commutativity of `heckeT_p_all` and `heckeT_q_all` on
the χ-space with **no new combinatorics** — the direct coset proof
`heckeT_p_all_comm_distinct` is bypassed entirely on this eigenspace. -/
section OperatorCommutativityFromRing

variable {k : ℤ} {χ : (ZMod N)ˣ →* ℂˣ}

/-- **The χ-twisted operators commute (from the ring).** Mirrors
`heckeRingHomCharSpaceOne_commute`: since the source ring `𝕋 (Gamma0_pair N) ℤ` is
commutative (`Gamma0_pair_HeckeAlgebra_mul_comm`) and `heckeRingHomCharSpace` is a ring hom, its
image in `Module.End ℂ (modFormCharSpace k χ)` is commutative. -/
theorem heckeRingHomCharSpace_commute (T₁ T₂ : 𝕋 (Gamma0_pair N) ℤ) :
    Commute (heckeRingHomCharSpace (k := k) (χ := χ) T₁)
      (heckeRingHomCharSpace (k := k) (χ := χ) T₂) := by
  show heckeRingHomCharSpace (k := k) (χ := χ) T₁ * heckeRingHomCharSpace (k := k) (χ := χ) T₂ =
    heckeRingHomCharSpace (k := k) (χ := χ) T₂ * heckeRingHomCharSpace (k := k) (χ := χ) T₁
  rw [← map_mul, ← map_mul, Gamma0_pair_HeckeAlgebra_mul_comm]

/-- **Endomorphism form of the normalization bridge.** On the χ-space, the canonical χ-twisted
operator at the prime double coset `D_p` equals the scalar `χ(p)⁻¹` times the restricted
concrete operator `heckeT_p_all_charRestrict`. This lifts the function-level
`heckeRingHomCharSpace_D_p_eq_heckeT_p_all` to an equality of endomorphisms of
`modFormCharSpace k χ`. -/
theorem heckeRingHomCharSpace_D_p_eq_scalar_charRestrict (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) :
    heckeRingHomCharSpace (k := k) (χ := χ) (T_single (Gamma0_pair N) ℤ (D_p_Gamma0 N p hp.pos) 1) =
      ((↑(χ (ZMod.unitOfCoprime p hpN)) : ℂ)⁻¹) • heckeT_p_all_charRestrict k p hp χ := by
  refine LinearMap.ext fun f => ?_
  apply Subtype.ext
  apply DFunLike.coe_injective
  show (⇑((heckeRingHomCharSpace (k := k) (χ := χ) (T_single (Gamma0_pair N) ℤ
      (D_p_Gamma0 N p hp.pos) 1) f : modFormCharSpace k χ) :
      ModularForm ((Gamma1 N).map (mapGL ℝ)) k) : ℍ → ℂ) = _
  rw [heckeRingHomCharSpace_D_p_eq_heckeT_p_all p hp hpN f]
  rfl

/-- The restricted concrete operator `heckeT_p_all_charRestrict` written as `χ(p)` times
the canonical operator at `D_p` (inverse of `heckeRingHomCharSpace_D_p_eq_scalar_charRestrict`,
with the invertible scalar `χ(p)` cancelled). -/
theorem heckeT_p_all_charRestrict_eq_scalar_heckeRingHom (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) :
    heckeT_p_all_charRestrict k p hp χ =
      (↑(χ (ZMod.unitOfCoprime p hpN)) : ℂ) •
        heckeRingHomCharSpace (k := k) (χ := χ)
          (T_single (Gamma0_pair N) ℤ (D_p_Gamma0 N p hp.pos) 1) := by
  rw [heckeRingHomCharSpace_D_p_eq_scalar_charRestrict p hp hpN, smul_smul,
    mul_inv_cancel₀ (Units.ne_zero _), one_smul]

/-- **Operator commutativity, as endomorphisms.** For good
primes `p ≠ q` (both `∤ N`), the restricted concrete Hecke operators
`heckeT_p_all_charRestrict` on `modFormCharSpace k χ` commute. Derived purely from the
ring: each equals an invertible scalar times the canonical operator
(`heckeT_p_all_charRestrict_eq_scalar_heckeRingHom`), and these operators commute
(`heckeRingHomCharSpace_commute`); scalars commute with everything. No coset combinatorics. -/
theorem heckeT_p_all_charRestrict_commute_via_ring
    {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpN : Nat.Coprime p N) (hqN : Nat.Coprime q N) :
    Commute (heckeT_p_all_charRestrict k p hp χ) (heckeT_p_all_charRestrict k q hq χ) := by
  rw [heckeT_p_all_charRestrict_eq_scalar_heckeRingHom p hp hpN,
    heckeT_p_all_charRestrict_eq_scalar_heckeRingHom q hq hqN]
  exact ((heckeRingHomCharSpace_commute (k := k) (χ := χ) _ _).smul_left _).smul_right _

/-- **Operator commutativity, function form**, packaged for the
concrete operators. For good primes `p ≠ q` (both `∤ N`) and `f ∈ modFormCharSpace k χ`,
the concrete operators `heckeT_p_all` and `heckeT_q_all` commute on `f`. Derived from
`heckeT_p_all_charRestrict_commute_via_ring` (a ring corollary), bypassing the direct
coset proof `heckeT_p_all_comm_distinct` on the χ-eigenspace. -/
theorem heckeT_p_all_comm_on_charSpace_via_ring
    {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpN : Nat.Coprime p N) (hqN : Nat.Coprime q N)
    (f : modFormCharSpace k χ) :
    heckeT_p_all k p hp (heckeT_p_all k q hq (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)) =
      heckeT_p_all k q hq (heckeT_p_all k p hp
        (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)) := by
  -- The ring-derived commutativity of the restricted operators.
  have hcomm := heckeT_p_all_charRestrict_commute_via_ring (k := k) (χ := χ) hp hq hpN hqN
  -- Apply at `f` and read off the underlying-form equality.
  have := congrArg (fun (T : Module.End ℂ (modFormCharSpace k χ)) => T f) hcomm
  exact congrArg (Subtype.val) this

end OperatorCommutativityFromRing

/-! ## The composite-`n` modular-form bridge

We extend the prime bridge `heckeRingHomCharSpace_D_p_eq_heckeT_p_all` to all `n`
coprime to `N`, identifying the concrete operator `heckeT_n` (restricted to the
`χ`-eigenspace via `heckeT_n_charRestrict`) with the canonical ring action
`heckeRingHomCharSpace` applied to an explicit ring element `heckeRingD_n`, up to the
scalar `χ(n)`.

The strategy mirrors the algebraic structure of `heckeT_n`:
* the prime double coset `D_p_Gamma0` is the ring-side generator `heckeRingDp`;
* the scalar coset `T(p,p)` is `heckeRingTpp`;
* prime powers are assembled by the same recurrence as `heckeT_ppow`
  (`heckeRingD_ppow`), and the bridge is proven by induction matching the recurrences,
  with the diamond term `⟨p⟩ = χ(p)` collapsing the χ-scalar;
* composites are assembled by coprime multiplicativity (`heckeT_n_charRestrict_mul_coprime`
  on the concrete side, `map_mul` on the ring side).
-/
section CompositeBridge

variable {k : ℤ} {χ : (ZMod N)ˣ →* ℂˣ}

/-- The ring-side prime generator: the single double coset `D_p`. -/
noncomputable def heckeRingDp (p : ℕ) (hp : 0 < p) : 𝕋 (Gamma0_pair N) ℤ :=
  T_single (Gamma0_pair N) ℤ (D_p_Gamma0 N p hp) 1

/-- The ring-side scalar generator: the single scalar double coset `T(p,p)`. -/
noncomputable def heckeRingTpp (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) :
    𝕋 (Gamma0_pair N) ℤ :=
  T_single (Gamma0_pair N) ℤ (T_diag_Gamma0 N (fun _ : Fin 2 => p) (fun _ => hp.pos)
    (by rw [Int.gcd_natCast_natCast]; exact hpN)) 1

/-- The ring-side prime-power element, built by the same recurrence as `heckeT_ppow`:
`D_{p^0} = 1`, `D_{p^1} = D_p`, and
`D_{p^{r+2}} = D_p · D_{p^{r+1}} − p · (T(p,p) · D_{p^r})`. -/
noncomputable def heckeRingD_ppow (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) :
    ℕ → 𝕋 (Gamma0_pair N) ℤ
  | 0 => 1
  | 1 => heckeRingDp p hp.pos
  | r + 2 =>
    heckeRingDp p hp.pos * heckeRingD_ppow p hp hpN (r + 1) -
      (p : ℤ) • (heckeRingTpp p hp hpN * heckeRingD_ppow p hp hpN r)

@[simp] theorem heckeRingD_ppow_zero (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) :
    heckeRingD_ppow (N := N) p hp hpN 0 = 1 := rfl

@[simp] theorem heckeRingD_ppow_one (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) :
    heckeRingD_ppow (N := N) p hp hpN 1 = heckeRingDp p hp.pos := rfl

theorem heckeRingD_ppow_succ_succ (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (r : ℕ) :
    heckeRingD_ppow (N := N) p hp hpN (r + 2) =
      heckeRingDp p hp.pos * heckeRingD_ppow p hp hpN (r + 1) -
        (p : ℤ) • (heckeRingTpp p hp hpN * heckeRingD_ppow p hp hpN r) := rfl

/-! ### The restricted prime-power operator on the χ-space

`heckeT_ppow k p hp r` preserves `modFormCharSpace k χ` (`heckeT_ppow_preserves_charSpace`,
re-proven here as it is `private` upstream), so it restricts to an endomorphism. -/

/-- The diamond operator `⟨d⟩` preserves `modFormCharSpace k χ` (it acts by the
scalar `χ(d)`). -/
theorem diamondOp_preserves_charSpace (d : (ZMod N)ˣ)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ modFormCharSpace k χ) :
    diamondOp k d f ∈ modFormCharSpace k χ := by
  have : diamondOp k d f = (↑(χ d) : ℂ) • f :=
    (mem_modFormCharSpace_iff k χ f).mp hf d
  rw [this]
  exact Submodule.smul_mem _ _ hf

/-- `heckeT_ppow k p hp r` (for `p ∤ N`) preserves `modFormCharSpace k χ`. (Local
re-proof; the upstream `heckeT_ppow_preserves_charSpace` is `private`.) -/
theorem heckeT_ppow_preserves_charSpace' (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) (r : ℕ)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ modFormCharSpace k χ) :
    heckeT_ppow k p hp r f ∈ modFormCharSpace k χ := by
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    match r, ih with
    | 0, _ => simpa using hf
    | 1, _ =>
      rw [heckeT_ppow_one]; exact heckeT_p_all_preserves_modFormCharSpace k p hp χ hf
    | (r + 2), ih =>
      rw [heckeT_ppow_succ_succ]
      have ih1 : heckeT_ppow k p hp (r + 1) f ∈ modFormCharSpace k χ := ih (r + 1) (by omega)
      have ihr : heckeT_ppow k p hp r f ∈ modFormCharSpace k χ := ih r (by omega)
      refine Submodule.sub_mem _ (heckeT_p_all_preserves_modFormCharSpace k p hp χ ih1) ?_
      refine Submodule.smul_mem _ _ ?_
      rw [Module.End.mul_apply, diamondOp_ext_coprime k hpN]
      exact diamondOp_preserves_charSpace _ ihr

/-- `heckeT_ppow k p hp r` (for `p ∤ N`) restricted to `modFormCharSpace k χ` as a
`ℂ`-linear endomorphism. -/
noncomputable def heckeT_ppow_charRestrict (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) (r : ℕ) : Module.End ℂ (modFormCharSpace k χ) where
  toFun f := ⟨heckeT_ppow k p hp r (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k),
    heckeT_ppow_preserves_charSpace' p hp hpN r f.property⟩
  map_add' f₁ f₂ := by
    apply Subtype.ext
    show heckeT_ppow k p hp r ((f₁ + f₂ : modFormCharSpace k χ) :
        ModularForm ((Gamma1 N).map (mapGL ℝ)) k) =
      heckeT_ppow k p hp r (f₁ : ModularForm _ k) + heckeT_ppow k p hp r (f₂ : ModularForm _ k)
    rw [show ((f₁ + f₂ : modFormCharSpace k χ) : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) =
      (f₁ : ModularForm _ k) + (f₂ : ModularForm _ k) from rfl, map_add]
  map_smul' c f := by
    apply Subtype.ext
    show heckeT_ppow k p hp r ((c • f : modFormCharSpace k χ) :
        ModularForm ((Gamma1 N).map (mapGL ℝ)) k) =
      c • heckeT_ppow k p hp r (f : ModularForm _ k)
    rw [show ((c • f : modFormCharSpace k χ) : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) =
      c • (f : ModularForm _ k) from rfl, map_smul]

@[simp] lemma heckeT_ppow_charRestrict_coe (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) (r : ℕ) (f : modFormCharSpace k χ) :
    ((heckeT_ppow_charRestrict (k := k) (χ := χ) p hp hpN r f : modFormCharSpace k χ) :
        ModularForm ((Gamma1 N).map (mapGL ℝ)) k) =
      heckeT_ppow k p hp r (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) := rfl

@[simp] theorem heckeT_ppow_charRestrict_zero (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) :
    heckeT_ppow_charRestrict (k := k) (χ := χ) p hp hpN 0 = 1 := by
  refine LinearMap.ext fun f => Subtype.ext ?_
  rw [heckeT_ppow_charRestrict_coe]; simp

@[simp] theorem heckeT_ppow_charRestrict_one (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) :
    heckeT_ppow_charRestrict (k := k) (χ := χ) p hp hpN 1 =
      heckeT_p_all_charRestrict k p hp χ := by
  refine LinearMap.ext fun f => Subtype.ext ?_
  rw [heckeT_ppow_charRestrict_coe, heckeT_p_all_charRestrict_coe, heckeT_ppow_one]

/-- The endomorphism recurrence for `heckeT_ppow_charRestrict`, with the diamond term
collapsed to the scalar `χ(p)` on the χ-space. -/
theorem heckeT_ppow_charRestrict_succ_succ (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) (r : ℕ) :
    heckeT_ppow_charRestrict (k := k) (χ := χ) p hp hpN (r + 2) =
      heckeT_p_all_charRestrict k p hp χ * heckeT_ppow_charRestrict p hp hpN (r + 1) -
        ((↑(χ (ZMod.unitOfCoprime p hpN)) : ℂ) * (p : ℂ) ^ (k - 1)) •
          heckeT_ppow_charRestrict p hp hpN r := by
  refine LinearMap.ext fun f => Subtype.ext ?_
  -- Unfold the char-restriction on the LHS, then its defining recurrence.
  rw [heckeT_ppow_charRestrict_coe, heckeT_ppow_succ_succ]
  -- Unfold all the endomorphism operations and char-restrictions on the RHS.
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply,
    Submodule.coe_sub, Submodule.coe_smul_of_tower, heckeT_p_all_charRestrict_coe,
    heckeT_ppow_charRestrict_coe]
  -- The diamond term collapses to χ(p) on the χ-space.
  have hdiam : diamondOp_ext k p
        (heckeT_ppow k p hp r (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)) =
      (↑(χ (ZMod.unitOfCoprime p hpN)) : ℂ) •
        heckeT_ppow k p hp r (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) := by
    rw [diamondOp_ext_coprime k hpN]
    exact (mem_modFormCharSpace_iff k χ
      (heckeT_ppow k p hp r (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k))).mp
      (heckeT_ppow_preserves_charSpace' p hp hpN r f.property) (ZMod.unitOfCoprime p hpN)
  rw [hdiam, smul_smul, mul_comm ((↑p : ℂ) ^ (k - 1)) (↑(χ (ZMod.unitOfCoprime p hpN)) : ℂ)]

/-! ### The ring-side generators as scalars times the restricted operators -/

/-- `heckeRingHomCharSpace` of the prime generator `D_p` equals `χ(p)⁻¹` times the
restricted prime operator (endomorphism form). -/
theorem heckeRingHomCharSpace_heckeRingDp (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) :
    heckeRingHomCharSpace (k := k) (χ := χ) (heckeRingDp p hp.pos) =
      ((↑(χ (ZMod.unitOfCoprime p hpN)) : ℂ))⁻¹ • heckeT_p_all_charRestrict k p hp χ :=
  heckeRingHomCharSpace_D_p_eq_scalar_charRestrict p hp hpN

/-- `heckeRingHomCharSpace` of the scalar generator `T(p,p)` is the scalar
`χ(p)⁻¹ · p^(k-2)` (endomorphism form). -/
theorem heckeRingHomCharSpace_heckeRingTpp (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) :
    heckeRingHomCharSpace (k := k) (χ := χ) (heckeRingTpp p hp hpN) =
      ((↑(χ (ZMod.unitOfCoprime p hpN)) : ℂ)⁻¹ * (p : ℂ) ^ (k - 2)) •
        (1 : Module.End ℂ (modFormCharSpace k χ)) := by
  refine LinearMap.ext fun f => ?_
  apply Subtype.ext
  apply DFunLike.coe_injective
  show (⇑((heckeRingHomCharSpace (k := k) (χ := χ) (T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N (fun _ : Fin 2 => p) (fun _ => hp.pos)
        (by rw [Int.gcd_natCast_natCast]; exact hpN)) 1) f : modFormCharSpace k χ) :
      ModularForm ((Gamma1 N).map (mapGL ℝ)) k) : ℍ → ℂ) = _
  rw [heckeRingHomCharSpace_T_pp_eq_scalar p hp hpN f]
  rfl

/-! ### The prime-power bridge

For `p ∤ N`, `heckeRingHomCharSpace (D_{p^r}) = (χ(p)⁻¹)^r • heckeT_ppow_charRestrict r`.
Proven by strong induction matching the two recurrences; the χ-powers thread through
because the diamond term contributes `χ(p)` (collapsing one inverse power) and the
prime term contributes one inverse power per step. -/

/-- **Prime-power bridge (endomorphism form).** -/
theorem heckeRingHomCharSpace_heckeRingD_ppow (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) (r : ℕ) :
    heckeRingHomCharSpace (k := k) (χ := χ) (heckeRingD_ppow p hp hpN r) =
      ((↑(χ (ZMod.unitOfCoprime p hpN)) : ℂ)⁻¹) ^ r •
        heckeT_ppow_charRestrict (k := k) (χ := χ) p hp hpN r := by
  set c : ℂ := (↑(χ (ZMod.unitOfCoprime p hpN)) : ℂ) with hc
  have hcne : c ≠ 0 := by rw [hc]; exact_mod_cast Units.ne_zero _
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    match r, ih with
    | 0, _ => simp [heckeRingD_ppow_zero, heckeT_ppow_charRestrict_zero]
    | 1, _ =>
      rw [heckeRingD_ppow_one, heckeT_ppow_charRestrict_one, pow_one,
        heckeRingHomCharSpace_heckeRingDp p hp hpN]
    | (r + 2), ih =>
      have ih1 := ih (r + 1) (by omega)
      have ihr := ih r (by omega)
      rw [heckeRingD_ppow_succ_succ, map_sub, map_mul, map_zsmul, map_mul,
        heckeRingHomCharSpace_heckeRingDp p hp hpN,
        heckeRingHomCharSpace_heckeRingTpp p hp hpN, ih1, ihr,
        heckeT_ppow_charRestrict_succ_succ p hp hpN r]
      -- Pull all scalars out of the operator compositions.
      simp only [smul_mul_assoc, mul_smul_comm, one_mul, smul_smul, smul_sub, ← hc]
      -- Convert the integer scalar `(↑p : ℤ) •` to the complex scalar `(p : ℂ) •`.
      rw [show ((↑p : ℤ) • ((c⁻¹ ^ r * (c⁻¹ * (↑p : ℂ) ^ (k - 2))) •
          heckeT_ppow_charRestrict (k := k) (χ := χ) p hp hpN r)) =
        ((p : ℂ) * (c⁻¹ ^ r * (c⁻¹ * (↑p : ℂ) ^ (k - 2)))) •
          heckeT_ppow_charRestrict (k := k) (χ := χ) p hp hpN r from by
        rw [← Int.cast_smul_eq_zsmul ℂ, smul_smul]; norm_cast]
      -- Reduce to scalar identities on the two (identical) operators.
      have hpne : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.pos.ne'
      -- prime-term coefficient: `c⁻¹^{r+1} · c⁻¹ = c⁻¹^{r+2}`.
      have h1 : c⁻¹ ^ (r + 1) * c⁻¹ = c⁻¹ ^ (r + 2) := (pow_succ c⁻¹ (r + 1)).symm
      -- R-term coefficient: `p · c⁻¹^r · c⁻¹ · p^{k-2} = c⁻¹^{r+2} · c · p^{k-1}`.
      have h2 : (p : ℂ) * (c⁻¹ ^ r * (c⁻¹ * (p : ℂ) ^ (k - 2))) =
          c⁻¹ ^ (r + 2) * (c * (p : ℂ) ^ (k - 1)) := by
        rw [show (c⁻¹ ^ (r + 2) * (c * (p : ℂ) ^ (k - 1))) =
          (c⁻¹ ^ (r + 1) * (c⁻¹ * c)) * (p : ℂ) ^ (k - 1) from by rw [pow_succ]; ring,
          inv_mul_cancel₀ hcne, mul_one, pow_succ,
          show (k - 1) = (k - 2) + 1 from by ring, zpow_add₀ hpne, zpow_one]
        ring
      rw [h1, h2]

/-! ### From prime powers to composite `n` via coprime multiplicativity

`heckeT_n_charRestrict` is multiplicative over coprime factors (from `heckeT_n_mul_coprime`),
and on a prime power `p^v` it agrees with `heckeT_ppow_charRestrict`. Combining with the
prime-power bridge gives the composite bridge. -/

/-- On a prime power `p^v` (good `p ∤ N`), `heckeT_n_charRestrict` agrees with the
prime-power restriction `heckeT_ppow_charRestrict`. -/
theorem heckeT_n_charRestrict_ppow (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (v : ℕ) (hv : 0 < v) :
    haveI : NeZero (p ^ v) := ⟨(pow_pos hp.pos v).ne'⟩
    heckeT_n_charRestrict k (p ^ v) (hpN.pow_left v) χ =
      heckeT_ppow_charRestrict (k := k) (χ := χ) p hp hpN v := by
  haveI : NeZero (p ^ v) := ⟨(pow_pos hp.pos v).ne'⟩
  refine LinearMap.ext fun f => Subtype.ext ?_
  rw [heckeT_n_charRestrict_coe, heckeT_ppow_charRestrict_coe, heckeT_n_prime_pow k hp v hv]

/-- `heckeT_n_charRestrict` is multiplicative over coprime factors. -/
theorem heckeT_n_charRestrict_mul_coprime (m n : ℕ) [NeZero m] [NeZero n]
    (hm : Nat.Coprime m N) (hn : Nat.Coprime n N) (hmn : Nat.Coprime m n) :
    haveI : NeZero (m * n) := ⟨Nat.mul_ne_zero (NeZero.ne m) (NeZero.ne n)⟩
    heckeT_n_charRestrict k (m * n) (Nat.Coprime.mul_left hm hn) χ =
      heckeT_n_charRestrict k m hm χ * heckeT_n_charRestrict k n hn χ := by
  haveI : NeZero (m * n) := ⟨Nat.mul_ne_zero (NeZero.ne m) (NeZero.ne n)⟩
  refine LinearMap.ext fun f => Subtype.ext ?_
  rw [heckeT_n_charRestrict_coe]
  simp only [Module.End.mul_apply, heckeT_n_charRestrict_coe]
  rw [heckeT_n_mul_coprime k m n hmn]
  rfl

/-- The χ-character is multiplicative on coprime parts: for `m, n` coprime to `N` and to
each other, `χ(unitOfCoprime (mn)) = χ(unitOfCoprime m) · χ(unitOfCoprime n)`. -/
theorem chi_unitOfCoprime_mul (χ : (ZMod N)ˣ →* ℂˣ) {m n : ℕ}
    (hm : Nat.Coprime m N) (hn : Nat.Coprime n N) :
    (↑(χ (ZMod.unitOfCoprime (m * n) (Nat.Coprime.mul_left hm hn))) : ℂ) =
      (↑(χ (ZMod.unitOfCoprime m hm)) : ℂ) * (↑(χ (ZMod.unitOfCoprime n hn)) : ℂ) := by
  rw [← Units.val_mul, ← map_mul]
  congr 2
  ext
  push_cast [ZMod.coe_unitOfCoprime]
  ring

/-- The χ-character on a prime power: `χ(unitOfCoprime (p^v)) = χ(unitOfCoprime p)^v`. -/
private lemma chi_unitOfCoprime_pow (χ : (ZMod N)ˣ →* ℂˣ) {p : ℕ} (v : ℕ)
    (hpN : Nat.Coprime p N) :
    (↑(χ (ZMod.unitOfCoprime (p ^ v) (hpN.pow_left v))) : ℂ) =
      (↑(χ (ZMod.unitOfCoprime p hpN)) : ℂ) ^ v := by
  rw [← Units.val_pow_eq_pow_val, ← map_pow]
  congr 2
  ext
  push_cast [ZMod.coe_unitOfCoprime]
  ring

/-- The χ-character splits over the prime-power / coprime-part decomposition `n = p^{v_p(n)}
· (n / p^{v_p(n)})`: `χ(unitOfCoprime n) = χ(unitOfCoprime p^{v_p(n)}) · χ(unitOfCoprime
(n/p^{v_p(n)}))`. -/
private lemma chi_eq_ordProj_mul_ordCompl (χ : (ZMod N)ˣ →* ℂˣ) {n : ℕ}
    (hn : Nat.Coprime n N) (p : ℕ)
    (hpvN : Nat.Coprime (p ^ n.factorization p) N)
    (hquotN : Nat.Coprime (n / p ^ n.factorization p) N) :
    (↑(χ (ZMod.unitOfCoprime n hn)) : ℂ) =
      (↑(χ (ZMod.unitOfCoprime (p ^ n.factorization p) hpvN)) : ℂ) *
        (↑(χ (ZMod.unitOfCoprime (n / p ^ n.factorization p) hquotN)) : ℂ) := by
  rw [← chi_unitOfCoprime_mul χ hpvN hquotN]
  congr 2
  refine Units.ext ?_
  rw [ZMod.coe_unitOfCoprime, ZMod.coe_unitOfCoprime, Nat.ordProj_mul_ordCompl_eq_self n p]

/-- The ring-side element `D_n` for general `n`, assembled by the same `minFac`-peeling
recursion as `heckeT_n` (`heckeT_n_aux`): `D_1 = 1`, and for `m > 1`,
`D_m = D_{p^v} · D_{m / p^v}` where `p = minFac m`, `v = v_p(m)`. -/
noncomputable def heckeRingD_n (n : ℕ) : 𝕋 (Gamma0_pair N) ℤ :=
  if h : n ≤ 1 then 1
  else
    let p := n.minFac
    let hp := Nat.minFac_prime (by omega : n ≠ 1)
    let v := n.factorization p
    -- The good-prime hypothesis is supplied at the bridge level; here we use a junk
    -- `0` when `p ∣ N` so the definition is total.
    (if hpN : Nat.Coprime p N then heckeRingD_ppow p hp hpN v else 0) *
      heckeRingD_n (n / p ^ v)
termination_by n
decreasing_by
  have hp := Nat.minFac_prime (by omega : n ≠ 1)
  exact Nat.div_lt_self (by omega) (Nat.one_lt_pow
    (hp.factorization_pos_of_dvd (by omega) (Nat.minFac_dvd n)).ne' hp.one_lt)

@[simp] theorem heckeRingD_n_one : heckeRingD_n (N := N) 1 = 1 := by
  rw [heckeRingD_n]; simp

/-- The `minFac`-peeling step for `heckeRingD_n` at a good smallest prime: for `n > 1` with
`p = minFac n` (coprime to `N`) and `v = v_p(n)`, `D_n = D_{p^v} · D_{n / p^v}`. -/
private lemma heckeRingD_n_peel (n p v : ℕ) (hn2 : 1 < n) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) (hpe : p = n.minFac) (hve : v = n.factorization p) :
    heckeRingD_n (N := N) n = heckeRingD_ppow p hp hpN v * heckeRingD_n (n / p ^ v) := by
  subst hpe hve
  conv_lhs => rw [heckeRingD_n]
  rw [dif_neg (by omega : ¬ n ≤ 1)]
  simp only [dif_pos hpN]

/-- The inductive step (`n > 1`) of the composite-`n` bridge: peel off the smallest prime
power `p^v` (`p = minFac n`, `v = v_p(n)`), apply the prime-power bridge and the strong
inductive hypothesis on `n / p^v`, then collect scalars via `χ(p^v) = χ(p)^v` and
`χ(n) = χ(p^v)·χ(n/p^v)`. -/
private lemma heckeRingHomCharSpace_heckeRingD_n_step (n : ℕ) [NeZero n] (hn1 : n ≠ 1)
    (hn : Nat.Coprime n N)
    (ih : ∀ m, m < n → (hm0 : NeZero m) → ∀ hm : Nat.Coprime m N,
      heckeRingHomCharSpace (k := k) (χ := χ) (heckeRingD_n m) =
        ((↑(χ (ZMod.unitOfCoprime m hm)) : ℂ))⁻¹ • heckeT_n_charRestrict k m hm χ) :
    heckeRingHomCharSpace (k := k) (χ := χ) (heckeRingD_n n) =
      ((↑(χ (ZMod.unitOfCoprime n hn)) : ℂ))⁻¹ • heckeT_n_charRestrict k n hn χ := by
  have hnpos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  set p := n.minFac with hp_def
  have hp : Nat.Prime p := Nat.minFac_prime hn1
  set v := n.factorization p with hv_def
  have hvpos : 0 < v := hp.factorization_pos_of_dvd hnpos.ne' (Nat.minFac_dvd n)
  have hpN : Nat.Coprime p N := hn.coprime_dvd_left (Nat.minFac_dvd n)
  have hpvN : Nat.Coprime (p ^ v) N := hpN.pow_left v
  have hquot_pos : 0 < n / p ^ v := Nat.div_pos
    (Nat.ordProj_le p hnpos.ne') (pow_pos hp.pos v)
  haveI : NeZero (n / p ^ v) := ⟨hquot_pos.ne'⟩
  haveI : NeZero (p ^ v) := ⟨(pow_pos hp.pos v).ne'⟩
  have hquotN : Nat.Coprime (n / p ^ v) N :=
    hn.coprime_dvd_left (Nat.div_dvd_of_dvd (Nat.ordProj_dvd n p))
  -- The two factors are coprime (the quotient drops all factors of `p`).
  have hcop : Nat.Coprime (p ^ v) (n / p ^ v) :=
    Nat.Coprime.pow_left v
      (hp.coprime_iff_not_dvd.mpr (hv_def ▸ Nat.not_dvd_ordCompl hp (NeZero.ne n)))
  -- Decompose the concrete operator the same way as `heckeRingD_n_peel`.
  have hTn : heckeT_n_charRestrict k n hn χ =
      heckeT_n_charRestrict k (p ^ v) hpvN χ *
        heckeT_n_charRestrict k (n / p ^ v) hquotN χ := by
    rw [← heckeT_n_charRestrict_mul_coprime (k := k) (χ := χ) (p ^ v) (n / p ^ v)
      hpvN hquotN hcop]
    congr 1
    exact (Nat.ordProj_mul_ordCompl_eq_self n p).symm
  -- Apply the prime-power bridge and the inductive hypothesis.
  rw [heckeRingD_n_peel n p v (by omega) hp hpN hp_def hv_def, map_mul,
    heckeRingHomCharSpace_heckeRingD_ppow p hp hpN v,
    ih (n / p ^ v) (Nat.div_lt_self (by omega)
        (Nat.one_lt_pow hvpos.ne' hp.one_lt)) ⟨hquot_pos.ne'⟩ hquotN,
    ← heckeT_n_charRestrict_ppow p hp hpN v hvpos]
  -- Collect scalars: `(χ(p)⁻¹)^v = χ(p^v)⁻¹` and `χ(n) = χ(p^v)·χ(n/p^v)`.
  rw [show (↑(χ (ZMod.unitOfCoprime p hpN)) : ℂ)⁻¹ ^ v =
      (↑(χ (ZMod.unitOfCoprime (p ^ v) hpvN)) : ℂ)⁻¹ from by
    rw [inv_pow, ← chi_unitOfCoprime_pow χ v hpN], smul_mul_smul_comm, hTn]
  congr 1
  rw [chi_eq_ordProj_mul_ordCompl χ hn p hpvN hquotN, mul_inv]

/-- **Composite-`n` bridge (endomorphism form).** For `n` coprime to `N`,
`heckeRingHomCharSpace (D_n) = χ(n)⁻¹ • heckeT_n_charRestrict k n hn χ`. Proven by
strong induction on `n` matching the `minFac`-peeling recursions, using coprime
multiplicativity (`heckeT_n_charRestrict_mul_coprime`, `chi_unitOfCoprime_mul`) and the
prime-power bridge (`heckeRingHomCharSpace_heckeRingD_ppow`). -/
theorem heckeRingHomCharSpace_heckeRingD_n (n : ℕ) [NeZero n] (hn : Nat.Coprime n N) :
    heckeRingHomCharSpace (k := k) (χ := χ) (heckeRingD_n n) =
      ((↑(χ (ZMod.unitOfCoprime n hn)) : ℂ))⁻¹ • heckeT_n_charRestrict k n hn χ := by
  -- Strong induction on a fully-quantified statement (so the `NeZero`/`hn` data does not
  -- block the induction tactic).
  suffices H : ∀ m : ℕ, (hm0 : NeZero m) → ∀ hm : Nat.Coprime m N,
      heckeRingHomCharSpace (k := k) (χ := χ) (heckeRingD_n m) =
        ((↑(χ (ZMod.unitOfCoprime m hm)) : ℂ))⁻¹ • heckeT_n_charRestrict k m hm χ by
    exact H n ‹NeZero n› hn
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn0 hn
    haveI : NeZero n := hn0
    by_cases hn1 : n = 1
    · -- n = 1
      subst hn1
      rw [heckeRingD_n_one, map_one]
      refine LinearMap.ext fun f => Subtype.ext ?_
      simp only [LinearMap.smul_apply, Module.End.one_apply, SetLike.val_smul,
        heckeT_n_charRestrict_coe, heckeT_n_one]
      rw [show (ZMod.unitOfCoprime 1 hn) = 1 from by ext; simp [ZMod.coe_unitOfCoprime]]
      simp
    · -- n > 1: peel off the smallest prime power (isolated as the `_step` lemma).
      exact heckeRingHomCharSpace_heckeRingD_n_step (k := k) (χ := χ) n hn1 hn ih

/-! ### Cusp connection: `cuspFormCharSpace ↪ modFormCharSpace`

These two results connect the cusp-form Hecke operators used in the definition of an
`Eigenform` to the canonical `Γ₀(N)` Hecke ring action `heckeRingHomCharSpace`.  They live
here (upstream of `Newforms.lean`) so that the `Eigenform` definition can take its
eigen-condition directly from the ring map.  They do not reference `Eigenform`. -/

/-- The modular-form coercion of a `χ`-cusp form lies in `modFormCharSpace k χ`.  The
diamond operator acts by the same slash on cusp forms and modular forms, so the
`χ`-eigenspace condition transfers verbatim. -/
theorem cuspFormCharSpace_toModularForm'_mem
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ) :
    f.toModularForm' ∈ modFormCharSpace k χ := by
  rw [mem_modFormCharSpace_iff]
  intro d
  -- The cusp-form eigenspace condition at `d` (`diamondOpCuspHom = diamondOpCusp`).
  have hcusp : diamondOpCusp k d f = (↑(χ d) : ℂ) • f :=
    diamondOpCusp_apply_charSpace k χ d hf
  -- `diamondOp` on the coercion equals the coercion of `diamondOpCusp`.
  show diamondOp k d f.toModularForm' = (↑(χ d) : ℂ) • f.toModularForm'
  rw [show diamondOp k d f.toModularForm' = (diamondOpCusp k d f).toModularForm' from by
    apply DFunLike.ext; intro τ; rfl, hcusp]
  rfl

/-- **Reverse of `cuspFormCharSpace_toModularForm'_mem`.** If the modular-form coercion of a
cusp form lies in `modFormCharSpace k χ`, then the cusp form itself lies in
`cuspFormCharSpace k χ`.  The diamond operators correspond under `toModularForm'`, which is
injective on the underlying function, so the eigenspace condition pulls back. -/
theorem cuspFormCharSpace_of_toModularForm'_mem
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f.toModularForm' ∈ modFormCharSpace k χ) :
    f ∈ cuspFormCharSpace k χ := by
  rw [mem_cuspFormCharSpace_iff]
  intro d
  -- The modular eigenspace condition at `d`.
  have hmod : diamondOp k d f.toModularForm' = (↑(χ d) : ℂ) • f.toModularForm' :=
    ((mem_modFormCharSpace_iff k χ f.toModularForm').mp hf) d
  -- `diamondOp` on the coercion is the coercion of `diamondOpCusp`; pull back via functions.
  show diamondOpCusp k d f = (↑(χ d) : ℂ) • f
  apply DFunLike.ext
  intro τ
  have := DFunLike.congr_fun hmod τ
  -- `diamondOp k d f.toModularForm' τ = (diamondOpCusp k d f).toModularForm' τ` by `rfl`.
  simpa using this

/-- **The eigenform operator is the ring image.** For a `χ`-cusp form `f` and `n` coprime
to `N`, `(heckeT_n_cusp k n f).toModularForm' = χ(n) • heckeRingHomCharSpace (heckeRingD_n n) (↑f)`
as elements of `modFormCharSpace k χ` (read on the modular-form side). -/
theorem heckeT_n_cusp_eq_heckeRingHom (n : ℕ) [NeZero n] (hn : Nat.Coprime n N)
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ) :
    (heckeT_n_cusp k n f).toModularForm' =
      (↑(χ (ZMod.unitOfCoprime n hn)) : ℂ) •
        (heckeRingHomCharSpace (k := k) (χ := χ) (heckeRingD_n n)
          ⟨f.toModularForm', cuspFormCharSpace_toModularForm'_mem hf⟩ :
          modFormCharSpace k χ).val := by
  -- The cusp operator is the modular operator on the coercion.
  rw [heckeT_n_cusp_toModularForm' n f]
  -- The composite-`n` bridge identifies the ring action with `χ(n)⁻¹ • heckeT_n`.
  have hbridge := heckeRingHomCharSpace_heckeRingD_n (k := k) (χ := χ) n hn
  have happ := congrArg (fun (T : Module.End ℂ (modFormCharSpace k χ)) =>
    (T ⟨f.toModularForm', cuspFormCharSpace_toModularForm'_mem hf⟩ : modFormCharSpace k χ).val)
    hbridge
  simp only [LinearMap.smul_apply, SetLike.val_smul, heckeT_n_charRestrict_coe] at happ
  -- `happ : (heckeRingHom (D_n) ⟨↑f, _⟩).val = χ(n)⁻¹ • heckeT_n n f.toModularForm'`.
  rw [happ, smul_smul, mul_inv_cancel₀ (by exact_mod_cast Units.ne_zero _), one_smul]

end CompositeBridge

end HeckeRing.GL2.Unified

