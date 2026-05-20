 /-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.HeckeRIngs.GL2.Unified.Core
import LeanModularForms.HeckeRIngs.GL2.Unified.Gamma1CharSpace
import LeanModularForms.HeckeRIngs.GL2.Unified.Gamma0Trivial
import LeanModularForms.HeckeRIngs.GL2.Unified.NebentypusSpace
import LeanModularForms.HeckeRIngs.GL2.Unified.CuspNebentypusSpace
import LeanModularForms.HeckeRIngs.GL2.Unified.CoprimeCommutativity
import LeanModularForms.HeckeRIngs.GL2.Unified.TwistedSlash
import LeanModularForms.HeckeRIngs.GL2.Unified.TwistedHeckeRing
import LeanModularForms.HeckeRIngs.GL2.Unified.Adjoint
import LeanModularForms.HeckeRIngs.GL2.Unified.Downstream
import LeanModularForms.HeckeRIngs.GL2.Unified.PrimeHeckeRing
import LeanModularForms.HeckeRIngs.GL2.Unified.GoodHeckeRing

/-!
# Experimental unified Hecke-operator layer

This module collects the separate-folder experimental API for packaging the
existing Hecke-operator constructions through a common `GoodHeckeFamily`
interface, together with transported `Γ₀(N), χ`-style models for modular and
cusp character spaces.

The current layer is deliberately conservative:

- it only packages the away-from-level operators already present in the repo;
- it does not alter the active SMO / adjoint-theory development path;
- it introduces no nonstandard assumptions and leaves the existing concrete
  operators as the mathematical source of truth.

It also now contains the direct function-space construction of the genuine
twisted `Γ₀(N),χ` action of the existing Hecke ring `𝕋 (Gamma0_pair N) ℤ`.
The remaining bridge work is to identify the concrete modular-form operators
with the corresponding images of that ring homomorphism.
-/
