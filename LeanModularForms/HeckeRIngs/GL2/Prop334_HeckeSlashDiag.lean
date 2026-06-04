/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GL2.Prop334_HeckeSlash
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

end HeckeRing.GL2
