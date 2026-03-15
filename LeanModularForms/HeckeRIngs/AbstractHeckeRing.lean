/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.AbstractHeckeRing.Basic
import LeanModularForms.HeckeRIngs.AbstractHeckeRing.Multiplication
import LeanModularForms.HeckeRIngs.AbstractHeckeRing.Module
import LeanModularForms.HeckeRIngs.AbstractHeckeRing.Associativity
import LeanModularForms.HeckeRIngs.AbstractHeckeRing.Ring
import LeanModularForms.HeckeRIngs.AbstractHeckeRing.Degree
import LeanModularForms.HeckeRIngs.AbstractHeckeRing.Commutativity

/-!
# Construction of Hecke rings following Shimura

This file re-exports the Hecke ring construction, split across:

* `Basic` — core definitions (`ArithmeticGroupPair`, `T'`, `M`, `decompQuot`, `𝕋`, `𝕄`)
* `Multiplication` — Shimura's multiplicity `m'`, `mulMap`, `mulSupport`, the `Mul` instance
* `Module` — `smulOrbit`, module action on left cosets, faithfulness
* `Associativity` — `IsScalarTower` (Shimura Prop 3.4)
* `Ring` — `Ring (𝕋 P ℤ)` instance and user-facing API
* `Degree` — degree ring homomorphism `deg : 𝕋 P ℤ →+* ℤ` (Shimura Prop 3.3)
-/
