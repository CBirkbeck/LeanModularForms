/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GL2.Prop334
import Mathlib.Data.ZMod.Units

/-!
# Prop 3.34 — Stabilizer surjectivity on diamond characters

For `g ∈ Δ₀(N)` with `gcd(det g, N) = 1`, the stabilizer subgroup
`(ConjAct g • (Gamma0_pair N).H).subgroupOf (Gamma0_pair N).H` maps surjectively onto
`(ZMod N)ˣ` under `Gamma0MapUnits`. This is a key step for the preservation of
`modFormCharSpace k χ` under `heckeSlash_gen` (Prop 3.34-E).

## Main results

* `Gamma0MapUnits_surjOn_stab_diag` — surjectivity for the diagonal case `g = diag(1, k)`,
  the case used by `heckeT_p` for `p` coprime to `N`.
* `Gamma0MapUnits_surjOn_stab_transport` — transports stabilizer surjectivity across the
  `Γ₀(N)`-double coset action, using abelianness of `(ZMod N)ˣ`.
* `Gamma0MapUnits_surjOn_stab_of_diagReduction` — general form, given a factorization
  `g = γ_L · diag(1, k) · γ_R` with `γ_L, γ_R ∈ H`.

## References

* Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §3.4.
-/

namespace HeckeRing.GL2.Prop334

open Matrix CongruenceSubgroup HeckeRing.GLn Matrix.SpecialLinearGroup HeckeRing.GL2

open scoped Pointwise MatrixGroups

/-- For `γ ∈ Γ₀(kN) ⊆ Γ₀(N)`, the nebentypus value at level `N` is the
image of the level-`kN` nebentypus value under `ZMod.unitsMap`. -/
lemma Gamma0MapUnits_unitsMap_of_Gamma0_mul (N k : ℕ) [NeZero N] [NeZero (k * N)]
    (γ : SL(2, ℤ)) (hγ_kN : γ ∈ Gamma0 (k * N))
    (hγ_N : γ ∈ Gamma0 N) :
    Gamma0MapUnits (⟨γ, hγ_N⟩ : ↥(Gamma0 N)) =
      ZMod.unitsMap (Nat.dvd_mul_left N k)
        (Gamma0MapUnits (⟨γ, hγ_kN⟩ : ↥(Gamma0 (k * N)))) := by
  apply Units.ext
  rw [Gamma0MapUnits_val, ZMod.unitsMap_val, Gamma0MapUnits_val]
  exact (ZMod.cast_intCast (Nat.dvd_mul_left N k) (γ.val 1 1)).symm

private lemma Gamma0MapUnits_conj_eq {N : ℕ} (a b : ↥(Gamma0 N)) :
    Gamma0MapUnits (a⁻¹ * b * a) = Gamma0MapUnits b := by
  rw [map_mul, map_mul, map_inv]
  exact inv_mul_cancel_comm _ _

private lemma mem_H_conj_of_source_stab {N : ℕ} [NeZero N]
    (g_target g_source γ_src_gl : GL (Fin 2) ℚ) (γ_L γ_R : (Gamma0_pair N).H)
    (h_eq : g_source = (γ_L : GL (Fin 2) ℚ) * g_target * (γ_R : GL (Fin 2) ℚ))
    (h_src : g_source⁻¹ * γ_src_gl * g_source ∈ (Gamma0_pair N).H) :
    g_target⁻¹ * ((γ_L : GL (Fin 2) ℚ)⁻¹ * γ_src_gl * (γ_L : GL (Fin 2) ℚ)) * g_target
      ∈ (Gamma0_pair N).H := by
  rw [show g_target⁻¹ * ((γ_L : GL (Fin 2) ℚ)⁻¹ * γ_src_gl * (γ_L : GL (Fin 2) ℚ)) * g_target =
    (γ_R : GL (Fin 2) ℚ) * (g_source⁻¹ * γ_src_gl * g_source) * (γ_R : GL (Fin 2) ℚ)⁻¹ from by
      subst h_eq; group]
  exact (Gamma0_pair N).H.mul_mem ((Gamma0_pair N).H.mul_mem γ_R.property h_src)
    ((Gamma0_pair N).H.inv_mem γ_R.property)

end HeckeRing.GL2.Prop334
