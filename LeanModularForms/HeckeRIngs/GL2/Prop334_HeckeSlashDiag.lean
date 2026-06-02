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

end HeckeRing.GL2
