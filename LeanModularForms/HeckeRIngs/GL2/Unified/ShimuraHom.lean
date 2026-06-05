/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GL2.Unified.NebentypusHeckeRingHom
import LeanModularForms.HeckeRIngs.GL2.Fricke

/-!
# The Shimura-convention Hecke action `Ψ_χ` as the Fricke conjugate of `Φ_χ`

The companion `heckeRingHomCharSpace` (`Φ_χ`) sends a `Γ₀(N)` double coset to the Hecke
operator of its *adjugate* class (a `V_p`-type operator at bad primes `p ∣ N`).  The
mathematically standard Shimura-convention action `Ψ_χ` is its **Fricke conjugate**:

`Ψ_χ(T) := E.symm ∘ Φ_{χ'}(T) ∘ E`,  where `E := frickeCharEquiv (χ := χ)` is the Fricke
isomorphism `M_k(N, χ) ≃ M_k(N, χ')` and `χ' := chiConj χ = χ ∘ (·)⁻¹`.

Because the Atkin–Lehner anti-involution `ι(δ) = W·adj(δ)·W⁻¹` swaps the right-coset
decomposition (on whose adjugates `Φ` is built) into the left-coset decomposition, this
conjugate is the genuine left-coset operator.  In particular, at a bad prime `p ∣ N`, the
slash representatives `W⁻¹·adj([[1,0],[Nr,p]])·W = [[1,r],[0,p]]` are exactly the `U_p`
representatives.

`Ψ_χ` is a ring homomorphism for free: conjugation by a `LinearEquiv` is an algebra
automorphism of `End`.

## Main definitions

* `conjEndRingHomFricke` — conjugation by `frickeCharEquiv` as a ring hom
  `End (M_k(N, χ')) →+* End (M_k(N, χ))`.
* `heckeRingHomCharSpaceShimura` (`Ψ_χ`) — the Shimura-convention Hecke ring action.

## References

* Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §3.4–3.5.
* Atkin–Lehner, *Hecke operators on `Γ₀(m)`*.
-/

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup HeckeRing.GLn
open HeckeRing
open scoped Pointwise MatrixGroups ModularForm UpperHalfPlane

namespace HeckeRing.GL2.Unified

open HeckeRing.GL2

variable {N : ℕ} [NeZero N]
variable {k : ℤ} {χ : (ZMod N)ˣ →* ℂˣ}

/-- Conjugation of an endomorphism of `M_k(N, chiConj χ)` by the Fricke isomorphism
`E = frickeCharEquiv (χ := χ)`, yielding an endomorphism of `M_k(N, χ)`:
`T ↦ E.symm ∘ T ∘ E`. -/
noncomputable def conjEndFricke (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (T : Module.End ℂ (modFormCharSpace k (chiConj χ))) :
    Module.End ℂ (modFormCharSpace k χ) :=
  (frickeCharEquiv k χ).symm.toLinearMap ∘ₗ T ∘ₗ (frickeCharEquiv k χ).toLinearMap

/-- Conjugation by `frickeCharEquiv` is a ring hom
`End (M_k(N, χ')) →+* End (M_k(N, χ))`. -/
noncomputable def conjEndRingHomFricke (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    Module.End ℂ (modFormCharSpace k (chiConj χ)) →+* Module.End ℂ (modFormCharSpace k χ) where
  toFun := conjEndFricke k χ
  map_one' := LinearMap.ext fun x ↦ by
    show (frickeCharEquiv k χ).symm
      ((1 : Module.End ℂ _) ((frickeCharEquiv k χ) x)) = x
    rw [Module.End.one_apply, LinearEquiv.symm_apply_apply]
  map_mul' S T := LinearMap.ext fun x ↦ by
    show (frickeCharEquiv k χ).symm ((S * T) ((frickeCharEquiv k χ) x)) =
      (frickeCharEquiv k χ).symm (S ((frickeCharEquiv k χ) ((frickeCharEquiv k χ).symm
        (T ((frickeCharEquiv k χ) x)))))
    rw [LinearEquiv.apply_symm_apply, Module.End.mul_apply]
  map_zero' := LinearMap.ext fun _ ↦ by simp [conjEndFricke]
  map_add' _ _ := LinearMap.ext fun _ ↦ by
    simp [conjEndFricke, LinearMap.add_apply, map_add]

@[simp] lemma conjEndRingHomFricke_apply (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (T : Module.End ℂ (modFormCharSpace k (chiConj χ))) :
    conjEndRingHomFricke (N := N) k χ T = conjEndFricke k χ T := rfl

/-- **The Shimura-convention Hecke action `Ψ_χ`** on the Nebentypus character space
`M_k(Γ₁(N), χ)`, as a ring homomorphism `𝕋(Γ₀(N)) →+* End_ℂ (M_k(Γ₁(N), χ))`.

It is the Fricke conjugate of the companion `Φ_{χ'}` (`heckeRingHomCharSpace` at the
inverse-conjugate character `χ' = chiConj χ`):
`Ψ_χ(T) = E.symm ∘ Φ_{χ'}(T) ∘ E`. -/
noncomputable def heckeRingHomCharSpaceShimura (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    𝕋 (Gamma0_pair N) ℤ →+* Module.End ℂ (modFormCharSpace k χ) :=
  (conjEndRingHomFricke (N := N) k χ).comp
    (heckeRingHomCharSpace (k := k) (χ := chiConj χ))

@[simp] lemma heckeRingHomCharSpaceShimura_apply (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (T : 𝕋 (Gamma0_pair N) ℤ) :
    heckeRingHomCharSpaceShimura (N := N) k χ T =
      conjEndFricke k χ (heckeRingHomCharSpace (k := k) (χ := chiConj χ) T) := rfl

/-! ## Reduction of `Ψ` at a single coset to the Fricke-conjugated twisted sum -/

/-- The single-coset Fricke-conjugation identity at the **function level**: for `f` in the
`χ`-Nebentypus space, the Shimura action `Ψ_χ(T_single D 1)` applied to `f`, as a function on
`ℍ`, equals the sum over the right-coset decomposition of `D` of the `χ'`-weighted slash by
the **`W`-conjugated** adjugate representatives `W · tRep_gen D i · W⁻¹` (`= ι(deltaRep_gen i)`,
the Atkin–Lehner image).  This is the clean algebraic core: the two Fricke factors `W`
contribute `W·(·)·W` per term, which equals `(W·(·)·W⁻¹) · W²`, and `W² = c·I` cancels the
`c⁻¹` from `E.symm`. -/
theorem heckeRingHomCharSpaceShimura_single_coe (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (D : HeckeCoset (Gamma0_pair N)) (f : modFormCharSpace k χ) :
    (⇑((heckeRingHomCharSpaceShimura (N := N) k χ (T_single (Gamma0_pair N) ℤ D 1) f :
        modFormCharSpace k χ) : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) : ℍ → ℂ) =
      ∑ i : decompQuot (Gamma0_pair N) (HeckeCoset.rep D),
        (↑(delta0NebentypusWeight (N := N) (chiConj χ) D i) : ℂ)⁻¹ •
          (⇑(f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) ∣[k]
            (frickeGL N * tRep_gen (Gamma0_pair N) D i * (frickeGL N)⁻¹ : GL (Fin 2) ℚ)) := by
  have hc := frickeScalar_ne_zero (N := N) (k := k)
  set Φf : modFormCharSpace k (chiConj χ) :=
    heckeRingHomCharSpace (k := k) (χ := chiConj χ) (T_single (Gamma0_pair N) ℤ D 1)
      (frickeCharEquiv k χ f) with hΦf
  -- Step 1: coe of `Ψ(D) f = E.symm (Φf)`.
  have hstep1 : (⇑((heckeRingHomCharSpaceShimura (N := N) k χ
        (T_single (Gamma0_pair N) ℤ D 1) f : modFormCharSpace k χ) :
        ModularForm ((Gamma1 N).map (mapGL ℝ)) k) : ℍ → ℂ) =
      (frickeScalar N k)⁻¹ •
        ((⇑(Φf : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) : ℍ → ℂ) ∣[k]
          (frickeGL N : GL (Fin 2) ℚ)) := by
    show (⇑((((frickeCharEquiv k χ).symm) Φf : modFormCharSpace k χ) :
        ModularForm ((Gamma1 N).map (mapGL ℝ)) k) : ℍ → ℂ) = _
    show (⇑((((frickeScalar N k)⁻¹ • frickeCharRestrict k (chiConj χ)) Φf :
        modFormCharSpace k χ) : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) : ℍ → ℂ) = _
    rw [LinearMap.smul_apply]
    show ((frickeScalar N k)⁻¹ • ⇑((frickeCharRestrict k (chiConj χ) Φf :
        modFormCharSpace k χ) : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) : ℍ → ℂ) = _
    rw [frickeCharRestrict_coe, frickeOperator_coe]
  -- Step 2: coe of `Φf = Φ_{χ'}(D)(E f)` as the twisted slash of `↑f ∣ W`.
  have hEf : (⇑((frickeCharEquiv k χ f : modFormCharSpace k (chiConj χ)) :
        ModularForm ((Gamma1 N).map (mapGL ℝ)) k) : ℍ → ℂ) =
      (⇑(f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) : ℍ → ℂ) ∣[k]
        (frickeGL N : GL (Fin 2) ℚ) := by
    show (⇑((frickeCharRestrict k χ f : modFormCharSpace k (chiConj χ)) :
        ModularForm ((Gamma1 N).map (mapGL ℝ)) k) : ℍ → ℂ) = _
    rw [frickeCharRestrict_coe, frickeOperator_coe]
  have hstep2 : (⇑(Φf : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) : ℍ → ℂ) =
      ∑ i : decompQuot (Gamma0_pair N) (HeckeCoset.rep D),
        (↑(delta0NebentypusWeight (N := N) (chiConj χ) D i) : ℂ)⁻¹ •
          ((⇑(f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) ∣[k]
            (frickeGL N : GL (Fin 2) ℚ)) ∣[k]
              tRep_gen (Gamma0_pair N) D i) := by
    have hΦf' : (Φf : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) =
        ((nebentypusHeckeSum (N := N) (k := k) (χ := chiConj χ)
          (T_single (Gamma0_pair N) ℤ D 1) (frickeCharEquiv k χ f) :
          modFormCharSpace k (chiConj χ)) : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) := rfl
    rw [hΦf', nebentypusHeckeSum_apply_coe, twistedHeckeSlashExt_gen,
      Finsupp.sum_single_index (by simp :
        (0 : ℤ) • twistedHeckeSlash_gen (N := N) k (chiConj χ) D
          (⇑(frickeCharEquiv k χ f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)) = 0),
      one_zsmul, twistedHeckeSlash_gen, hEf]
  -- Step 3: assemble, using the per-term identity `g ∣ (W · M · W) = c • (g ∣ (W · M · W⁻¹))`.
  rw [hstep1, hstep2, SlashAction.sum_slash, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [smul_slash_pos_det k _ _ _ frickeGL_det_pos, smul_smul,
    ← SlashAction.slash_mul, ← SlashAction.slash_mul,
    show (frickeGL N : GL (Fin 2) ℚ) * (tRep_gen (Gamma0_pair N) D i * frickeGL N) =
        (frickeGL N * tRep_gen (Gamma0_pair N) D i) * frickeGL N from by group,
    slash_mul_frickeGL, smul_smul,
    show (frickeGL N : GL (Fin 2) ℚ) * tRep_gen (Gamma0_pair N) D i * (frickeGL N)⁻¹ =
        frickeGL N * tRep_gen (Gamma0_pair N) D i * (frickeGL N)⁻¹ from rfl]
  congr 1
  rw [mul_assoc, mul_comm (↑(delta0NebentypusWeight (N := N) (chiConj χ) D i) : ℂ)⁻¹,
    ← mul_assoc, inv_mul_cancel₀ (frickeScalar_ne_zero (N := N) (k := k)), one_mul]

/-! ## The bad-prime payoff `Ψ(D_p) = U_p`

The matrix algebra is fully verified: at a bad prime `p ∣ N`, the right-coset representatives
of `D_p = Γ₀(N)·diag(1,p)·Γ₀(N)` are the lower-unipotent `δ_r = [[1,0],[N·r,p]]`
(`r = 0, …, p−1`; `lunip_inject` / `decompQuot_D_p_Gamma0_bad_natcard`), each with upper-left
unit `1` (so `χ'`-weight `1`), and the `W`-conjugated adjugate is exactly the `U_p`
representative:
`W · adj(δ_r) · W⁻¹ = W · [[p,0],[−N·r,1]] · W⁻¹ = [[1,r],[0,p]] = T_p_upper(r)`
(machine-checked above as a `GL₂(ℚ)` matrix identity).

Combined with `heckeRingHomCharSpaceShimura_single_coe`, this gives
`Ψ_χ(D_p)(f) = ∑_r (⇑f) ∣ T_p_upper(r) = U_p(f)`.  The remaining gap is the **index
bijection bookkeeping**: identifying `decompQuot`'s abstract index set with `Fin p` via the
explicit reps `lunip_inject` (currently `private` in `CongruenceHecke/Props.lean`), matching
`deltaRep_gen` to `[[1,0],[N·r,p]]`, and absorbing the residual `Γ₁(N)` factor (left of the
slash, killed by `f`'s `Γ₁(N)`-invariance).  This mirrors `twisted_matches_T_p` /
`twistedTpPsi` (the good-prime analogue) but on the `W`-conjugated bad reps. -/
theorem heckeRingHomCharSpaceShimura_D_p_bad (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (p : ℕ) (hp : Nat.Prime p) (hpN : ¬ Nat.Coprime p N) :
    heckeRingHomCharSpaceShimura (N := N) k χ (heckeRingDp p hp.pos) =
      heckeT_p_all_charRestrict k p hp χ := by
  refine LinearMap.ext fun f ↦ Subtype.ext (DFunLike.coe_injective ?_)
  show (⇑((heckeRingHomCharSpaceShimura (N := N) k χ
      (T_single (Gamma0_pair N) ℤ (D_p_Gamma0 N p hp.pos) 1) f : modFormCharSpace k χ) :
      ModularForm ((Gamma1 N).map (mapGL ℝ)) k) : ℍ → ℂ) =
    (⇑(heckeT_p_all k p hp (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)) : ℍ → ℂ)
  rw [heckeRingHomCharSpaceShimura_single_coe, heckeT_p_all_not_coprime_apply k hp hpN,
    heckeT_p_ut]
  -- REMAINING GAP (deliverable 7, precisely diagnosed): the bad-prime index-bijection identity
  --   `∑ᵢ wᵢ⁻¹ • (f ∣ (W · tRep_gen i · W⁻¹)) = ∑_{b<p} f ∣ T_p_upper(b)`.
  -- All non-combinatorial pieces are in place / verified:
  --  • LHS reduction `…_single_coe` (sorry-free above).
  --  • Per-rep matrix core (`Fricke.frickeGL_mul_adj_lunipRep_mul_frickeGL_inv`, sorry-free):
  --      `W · adj([[1,0],[N·r,p]]) · W⁻¹ = T_p_upper(r)`.
  --  • Cardinality `Nat.card (decompQuot …) = p` (`decompQuot_D_p_Gamma0_bad_natcard`,
  --      currently `private` in `NebentypusHeckeRingHom.lean`; de-privatise or replicate).
  --  • Weight `wᵢ = 1`: the bad reps `δ_r = [[1,0],[N·r,p]]` have upper-left unit `1`, so
  --      `delta0NebentypusWeight (chiConj χ) D_p i = 1` (cf. `adjLowerΔ_weight` pattern).
  -- What is missing is the index bijection `Fin p ≃ decompQuot (Gamma0_pair N) (rep D_p)`
  -- sending `b ↦ ⟦lunipRep p b⟧` (the bad-prime analogue of `twistedTpPsi`, built on the
  -- `private lunip_inject` of `CongruenceHecke/Props.lean`), plus the bookkeeping identifying
  -- `deltaRep_gen i` with `δ_r` up to a `Γ₀(N)`-correction that the adjugate turns into a left
  -- `Γ₁(N)`-factor absorbed by `f` (mirroring `weighted_value_eq` /
  -- `twisted_weighted_slash_tRep_gen_of_mem`, but on the `W`-conjugated reps).  This is a
  -- standalone ~250-LOC port of the good-prime `twisted_matches_T_p` apparatus.
  sorry

end HeckeRing.GL2.Unified
