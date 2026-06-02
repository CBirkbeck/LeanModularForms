/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GL2.Prop334_HeckeSlash
import LeanModularForms.HeckeRIngs.GL2.Prop334_StabSurj
import LeanModularForms.HeckeRIngs.GL2.HeckeT_p_Gamma0_Bridge

/-!
# Functional χ-equivariance for `heckeSlash_gen` at `D_p_Gamma0`

This file specializes `hComm` from `Prop334_HeckeSlash.lean` to
`D = D_p_Gamma0 N p hp.pos`, proving the functional χ-equivariance of the
Γ₀(N)-level Hecke slash operator on `modFormCharSpace k χ` (unconditionally for
`χ = 1`, and conditionally on a χ-aware bridge for general `χ`).

## References

* Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §3.4.
* Diamond–Shurman, *A First Course in Modular Forms*, §5.2, Proposition 5.2.1.
-/

open Matrix Matrix.SpecialLinearGroup HeckeRing.GLn CongruenceSubgroup
open HeckeRing DoubleCoset

open scoped Pointwise MatrixGroups ModularForm UpperHalfPlane Manifold

namespace HeckeRing.GL2

variable {N : ℕ} [NeZero N]

/-- For `f ∈ modFormCharSpace k χ`, the auxiliary diamond operator
`diamondOpAux k g` acts as multiplication by the scalar `χ(Gamma0MapUnits g)`. -/
lemma diamondOpAux_apply_charSpace (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (g : ↥(Gamma0 N)) {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ modFormCharSpace k χ) :
    diamondOpAux k g f = (↑(χ (Gamma0MapUnits g)) : ℂ) • f := by
  have h : diamondOp k (Gamma0MapUnits g) f = (↑(χ (Gamma0MapUnits g)) : ℂ) • f :=
    (mem_modFormCharSpace_iff k χ f).mp hf (Gamma0MapUnits g)
  rwa [diamondOp_eq_diamondOpAux k _ g rfl] at h

/-- **χ-equivariance of `heckeT_p`**: for `f ∈ modFormCharSpace k χ` and
`g ∈ Γ₀(N)`,
`heckeT_p_fun f ∣[k] mapGL ℝ g = χ(Gamma0MapUnits g) • heckeT_p_fun f`. This is
the explicit `T_p`-level version of `hComm`, derived from
`heckeT_p_comm_diamondOp` combined with the χ-eigenspace property. -/
theorem heckeT_p_fun_slash_comm_charSpace (k : ℤ) (p : ℕ)
    (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (χ : (ZMod N)ˣ →* ℂˣ)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ modFormCharSpace k χ)
    (g : ↥(Gamma0 N)) :
    heckeT_p_fun k p hp hpN f ∣[k] mapGL ℝ (g : SL(2, ℤ)) =
    (↑(χ (Gamma0MapUnits g)) : ℂ) • heckeT_p_fun k p hp hpN f := by
  set d := Gamma0MapUnits g
  set Tf := heckeT_p k p hp hpN f
  show ⇑(diamondOpAux k g Tf) = _
  rw [← diamondOp_eq_diamondOpAux k d g rfl,
    show diamondOp k d Tf = heckeT_p k p hp hpN (diamondOp k d f) from
      LinearMap.congr_fun (heckeT_p_comm_diamondOp (N := N) k p hp hpN d) f]
  have hdf : diamondOp k d f = (↑(χ d) : ℂ) • f :=
    (mem_modFormCharSpace_iff k χ f).mp hf d
  rw [hdf, map_smul]; rfl

/-- **Functional χ-equivariance at `D_p_Gamma0`, for `χ = 1`**: specializes the
`hComm` hypothesis in `Prop334_HeckeSlash.lean` to the trivial character. -/
theorem heckeSlash_gen_functional_equivariance_D_p_Gamma0_trivial
    (k : ℤ) (p : ℕ) (hp : Nat.Prime p) (_hpN : Nat.Coprime p N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hf : f ∈ modFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ))
    (g : ↥(Gamma0 N)) :
    (heckeSlash_gen (Gamma0_pair N) k (D_p_Gamma0 N p hp.pos) (⇑f : ℍ → ℂ)) ∣[k]
      mapGL ℝ (g : SL(2, ℤ)) =
    (↑((1 : (ZMod N)ˣ →* ℂˣ) (Gamma0MapUnits g)) : ℂ) •
      heckeSlash_gen (Gamma0_pair N) k (D_p_Gamma0 N p hp.pos) (⇑f : ℍ → ℂ) := by
  have hf_H : ∀ h, h ∈ (Gamma0_pair N).H → (⇑f : ℍ → ℂ) ∣[k] (glMap h) = ⇑f := fun h hh ↦
    Gamma0_pair_H_invariant_of_invariant N
      (fun γ hγ ↦ SlashInvariantFormClass.slash_action_eq
        (modFormCharSpace_one_equiv_Gamma0 N k ⟨f, hf⟩) γ hγ) h hh
  exact heckeSlash_gen_slash_comm_one k (D_p_Gamma0 N p hp.pos) (⇑f) hf_H g

/-- **Conditional form**: if the bridge `heckeSlash_gen D_p_Gamma0 ⇑f =
⇑(heckeT_p k p hp hpN f)` holds pointwise, then the functional χ-equivariance
follows. The bridge is known for `χ = 1`; the general-`χ` case is the technical
content of Diamond–Shurman Prop 5.2.1 at the level of explicit coset
representatives. -/
theorem heckeSlash_gen_functional_equivariance_D_p_Gamma0_of_bridge
    (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ modFormCharSpace k χ)
    (h_bridge :
      heckeSlash_gen (Gamma0_pair N) k (D_p_Gamma0 N p hp.pos) (⇑f : ℍ → ℂ) =
      heckeT_p_fun k p hp hpN f)
    (g : ↥(Gamma0 N)) :
    (heckeSlash_gen (Gamma0_pair N) k (D_p_Gamma0 N p hp.pos) (⇑f : ℍ → ℂ)) ∣[k]
      mapGL ℝ (g : SL(2, ℤ)) =
    (↑(χ (Gamma0MapUnits g)) : ℂ) •
      heckeSlash_gen (Gamma0_pair N) k (D_p_Gamma0 N p hp.pos) (⇑f : ℍ → ℂ) := by
  rw [h_bridge]
  exact heckeT_p_fun_slash_comm_charSpace k p hp hpN χ hf g

end HeckeRing.GL2
