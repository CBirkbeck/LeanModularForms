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
`D = D_p_Gamma0 N p hp.pos`.

## Strategy

For `f ∈ modFormCharSpace k χ`, we bridge the abstract Γ₀(N)-level Hecke
slash `heckeSlash_gen D_p_Gamma0 (⇑f)` to the Γ₁(N)-level explicit operator
`heckeT_p k p hp hpN f`, then apply `heckeT_p_comm_diamondOp` which proves
`T_p`-diamond-commutativity at the explicit `heckeT_p` level.

The bridge `heckeSlash_gen D_p_Gamma0 (⇑f) = ⇑(heckeT_p k p hp hpN f)` is
known for `χ = 1` (`heckeT_p_fun_eq_heckeSlash_gen_Gamma0_on_charSpace_one`).
For general `χ`, the bridge requires a χ-aware generalization of the matching
theorem `tRep_gen_D_p_Gamma0_matches_T_p_reps`.

## Main result (conditional on bridge)

Assuming the bridge `heckeT_p_fun_eq_heckeSlash_gen_Gamma0_on_charSpace` holds
for general `χ`, we prove `hComm` for `D = D_p_Gamma0 N p hp.pos`.

## References

* Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §3.4.
* Diamond–Shurman, *A First Course in Modular Forms*, §5.2, Proposition 5.2.1.
-/

open Matrix Matrix.SpecialLinearGroup HeckeRing.GLn CongruenceSubgroup
open HeckeRing DoubleCoset

open scoped Pointwise MatrixGroups ModularForm UpperHalfPlane Manifold

namespace HeckeRing.GL2

variable {N : ℕ} [NeZero N]

/-! ### Diamond scalar action on `modFormCharSpace k χ`

For `f ∈ modFormCharSpace k χ` and `g ∈ Γ₀(N)`, `diamondOpAux k g f = χ(Gamma0MapUnits g) • f`.
This is the direct consequence of the χ-eigenspace definition. -/

/-- For `f ∈ modFormCharSpace k χ`, the auxiliary diamond operator
`diamondOpAux k g` acts as multiplication by the scalar `χ(Gamma0MapUnits g)`. -/
lemma diamondOpAux_apply_charSpace (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (g : ↥(Gamma0 N)) {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ modFormCharSpace k χ) :
    diamondOpAux k g f = (↑(χ (Gamma0MapUnits g)) : ℂ) • f := by
  have h := (mem_modFormCharSpace_iff k χ f).mp hf (Gamma0MapUnits g)
  -- `h : diamondOpHom k (Gamma0MapUnits g) f = (↑(χ (Gamma0MapUnits g)) : ℂ) • f`.
  rwa [show diamondOpHom k (Gamma0MapUnits g) =
      diamondOp k (Gamma0MapUnits g) from rfl,
    diamondOp_eq_diamondOpAux k _ g rfl] at h

/-! ### χ-equivariance of `heckeT_p_fun` on `modFormCharSpace k χ`

Using `orbit_sum_comm` (which gives `heckeT_p_fun f ∣[k] mapGL ℝ g = heckeT_p_fun
(diamondOpAux k g f)`) and the scalar action of `diamondOpAux` on
`modFormCharSpace k χ`, we get the χ-equivariance at the `heckeT_p_fun`
level. This is the `heckeT_p`-level analogue of the `hComm` we need. -/

/-- **χ-equivariance of `heckeT_p`**: for `f ∈ modFormCharSpace k χ` and
`g ∈ Γ₀(N)`:
```
heckeT_p_fun k p hp hpN f ∣[k] mapGL ℝ g = χ(Gamma0MapUnits g) • heckeT_p_fun k p hp hpN f
```
This is the explicit `T_p`-level version of `hComm`, derived from
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
  -- Step 1: LHS equals `⇑(diamondOpAux k g Tf)`.
  have hLHS : heckeT_p_fun k p hp hpN f ∣[k] mapGL ℝ (g : SL(2, ℤ)) =
      ⇑(diamondOpAux k g Tf) := by
    -- Unfold `heckeT_p_fun` as `⇑Tf`.
    show (⇑Tf : ℍ → ℂ) ∣[k] mapGL ℝ (g : SL(2, ℤ)) = ⇑(diamondOpAux k g Tf)
    rfl
  rw [hLHS]
  -- Step 2: `diamondOpAux k g Tf = diamondOp k d Tf` (since `Gamma0MapUnits g = d`).
  have hdia_aux : diamondOpAux k g Tf = diamondOp k d Tf :=
    (diamondOp_eq_diamondOpAux k d g rfl).symm.symm ▸ rfl
  rw [hdia_aux]
  -- Step 3: `heckeT_p_comm_diamondOp` gives
  -- `diamondOp k d Tf = heckeT_p (diamondOp k d f)`.
  have h_comm := heckeT_p_comm_diamondOp (N := N) k p hp hpN d
  have h_apply_f : diamondOp k d Tf = heckeT_p k p hp hpN (diamondOp k d f) := by
    show (diamondOp k d).comp (heckeT_p k p hp hpN) f =
      (heckeT_p k p hp hpN).comp (diamondOp k d) f
    rw [h_comm]
  rw [h_apply_f]
  -- Step 4: For `f ∈ modFormCharSpace k χ`, `diamondOp k d f = χ(d) • f`.
  have hdf : diamondOp k d f = (↑(χ d) : ℂ) • f := by
    have := (mem_modFormCharSpace_iff k χ f).mp hf d
    simpa using this
  rw [hdf, map_smul]
  -- Step 5: Coercion to function level.
  rfl

/-! ### Functional χ-equivariance at `D_p_Gamma0`, via the χ=1 bridge

For `χ = 1`, we can prove the `hComm` hypothesis directly: the bridge
`heckeT_p_fun_eq_heckeSlash_gen_Gamma0_on_charSpace_one` combined with
`heckeT_p_fun_slash_comm_charSpace` at `χ = 1` gives the result. -/

/-- **Functional χ-equivariance at `D_p_Gamma0`, for `χ = 1`**: this
specializes the `hComm` hypothesis in `Prop334_HeckeSlash.lean` to the
trivial character. It is provable directly from the existing
`heckeT_p_fun_eq_heckeSlash_gen_Gamma0_on_charSpace_one` bridge. -/
theorem heckeSlash_gen_functional_equivariance_D_p_Gamma0_trivial
    (k : ℤ) (p : ℕ) (hp : Nat.Prime p) (_hpN : Nat.Coprime p N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hf : f ∈ modFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ))
    (g : ↥(Gamma0 N)) :
    (heckeSlash_gen (Gamma0_pair N) k (D_p_Gamma0 N p hp.pos) (⇑f : ℍ → ℂ)) ∣[k]
      mapGL ℝ (g : SL(2, ℤ)) =
    (↑((1 : (ZMod N)ˣ →* ℂˣ) (Gamma0MapUnits g)) : ℂ) •
      heckeSlash_gen (Gamma0_pair N) k (D_p_Gamma0 N p hp.pos) (⇑f : ℍ → ℂ) := by
  -- For χ = 1, `f ∈ modFormCharSpace k 1` means f is Γ₀(N)-invariant; reduces
  -- to the slash-invariance lemma.
  have hf_H : ∀ h, h ∈ (Gamma0_pair N).H → (⇑f : ℍ → ℂ) ∣[k] (glMap h) = ⇑f := by
    intro h hh
    set f_g0 : ModularForm ((Gamma0 N).map (mapGL ℝ)) k :=
      modFormCharSpace_one_equiv_Gamma0 N k ⟨f, hf⟩
    have hfg : (⇑f : ℍ → ℂ) = ⇑f_g0 := by rfl
    rw [hfg]
    exact Gamma0_pair_H_invariant_of_invariant N
      (fun γ hγ => SlashInvariantFormClass.slash_action_eq f_g0 γ hγ) h hh
  -- Apply `heckeSlash_gen_slash_comm_one`.
  exact heckeSlash_gen_slash_comm_one k (D_p_Gamma0 N p hp.pos) (⇑f) hf_H g

/-! ### The target theorem: functional χ-equivariance at `D_p_Gamma0`

The general-`χ` case requires a χ-aware bridge
`heckeSlash_gen D_p_Gamma0 (⇑f) = ⇑(heckeT_p k p hp hpN f)` for
`f ∈ modFormCharSpace k χ`. This bridge generalizes
`heckeT_p_fun_eq_heckeSlash_gen_Gamma0_on_charSpace_one` from `χ = 1` to
arbitrary `χ`.

### Conditional statement

The conditional form exposes the outstanding bridge hypothesis so that
downstream consumers (e.g., `heckeSlash_gen_mem_modFormCharSpace_of_slash_comm`
in `Prop334_HeckeSlash.lean`) can obtain the `hComm` hypothesis for
`D = D_p_Gamma0 N p hp.pos` once the bridge is established. -/

/-- **Conditional form**: if the bridge `heckeSlash_gen D_p_Gamma0 ⇑f =
⇑(heckeT_p k p hp hpN f)` holds pointwise, then the functional χ-equivariance
follows.

The bridge is known for `χ = 1` via
`heckeT_p_fun_eq_heckeSlash_gen_Gamma0_on_charSpace_one`; the general-`χ` case
is the technical content of Diamond–Shurman Prop 5.2.1 at the level of
explicit coset representatives, pending further formalization. -/
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
  -- Rewrite both sides via the bridge.
  rw [h_bridge]
  -- `χ(Gamma0MapUnits g) • heckeT_p_fun f = heckeT_p_fun f ∣[k] mapGL ℝ g`
  -- by `heckeT_p_fun_slash_comm_charSpace`.
  exact heckeT_p_fun_slash_comm_charSpace k p hp hpN χ hf g

/-! ### Summary

Completing the general-`χ` case reduces to the single technical step of
proving the bridge
```
heckeSlash_gen (Gamma0_pair N) k (D_p_Gamma0 N p hp.pos) (⇑f) = heckeT_p_fun k p hp hpN f
```
for `f ∈ modFormCharSpace k χ`. This bridge is the natural Γ₁(N)-level
restatement of the matching theorem `tRep_gen_D_p_Gamma0_matches_T_p_reps`
(currently proved only for Γ₀(N)-invariant functions, corresponding to
`χ = 1`), combined with the diamond identity
`slash_M_infty_eq_diamond_slash_T_p_lower`.

For `χ = 1`, the statement
`heckeSlash_gen_functional_equivariance_D_p_Gamma0_trivial` above is
unconditional. -/

end HeckeRing.GL2
