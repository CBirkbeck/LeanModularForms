/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: f5ac49f3-0d57-45ce-beca-62d2d5543d69

The following was proved by Aristotle:

- theorem generalizedWindingNumber_decomposition
    (γ : PiecewiseC1Immersion') (_hclosed : γ.toPiecewiseC1Curve'.IsClosed) (z₀ : ℂ)
    (zeros : Finset ℝ) (_hzeros : ∀ t ∈ zeros, t ∈ Icc γ.a γ.b ∧ γ.toFun t = z₀)
    (_hfinite : ∀ t ∈ Icc γ.a γ.b, γ.toFun t = z₀ → t ∈ zeros) :
    ∃ (γ_tilde : PiecewiseC1Curve') (angles : zeros → ℝ),
      generalizedWindingNumber γ.toFun γ.a γ.b z₀ =
      generalizedWindingNumber γ_tilde.toFun γ_tilde.a γ_tilde.b z₀ +
      ∑ t : zeros, (angles t : ℂ) / (2 * Real.pi)

- theorem windingNumberRealIntegrand_bounded
    (γ : PiecewiseC1Immersion') (a b : ℝ) :
    ∃ M : ℝ, ∀ t ∈ Icc a b, |windingNumberRealIntegrand γ.toFun t| ≤ M

- theorem windingNumberRealIntegrand_limit_at_zero
    (γ : PiecewiseC1Immersion')
    (t₀ : ℝ) (_ht₀ : t₀ ∈ Icc γ.a γ.b) (_hγ_zero : γ.toFun t₀ = 0)
    (_hC2 : ContDiffAt ℝ 2 γ.toFun t₀) :
    let κ

- theorem generalizedResidueTheorem
    (U : Set ℂ) (_hU : IsOpen U)
    (S : Set ℂ) (_hS : ∀ s ∈ S, s ∈ U) (_hS_discrete : ∀ s ∈ S, ∃ ε > 0, ∀ s' ∈ S, s' ≠ s → ε ≤ ‖s' - s‖)
    (f : ℂ → ℂ) (_hf : DifferentiableOn ℂ f (U \ S))
    (γ : PiecewiseC1Curve') (_hγ_closed : γ.IsClosed)
    -- Simple poles on C
    (_hSimplePoles : ∀ s ∈ S, ∀ t ∈ Icc γ.a γ.b, γ.toFun t = s →
      ∃ ε > 0, ∃ c : ℂ, ∀ z ∈ ball s ε \ {s}, f z = c / (z - s) + (f z - c / (z - s))) :
    CauchyPrincipalValueExists f γ.toFun γ.a γ.b 0 ∧
    cauchyPrincipalValue f γ.toFun γ.a γ.b 0 =
      2 * Real.pi * Complex.I * ∑ᶠ s ∈ S, generalizedWindingNumber γ.toFun γ.a γ.b s *
        (residue f s)

- theorem windingNumber_homotopy_invariant
    (Γ γ : ℝ → ℂ) (a b : ℝ) (_hab : a < b)
    (_hΓ : ContinuousOn Γ (Icc a b)) (_hγ : ContinuousOn γ (Icc a b))
    (H : ℝ × ℝ → ℂ) (_hH : Continuous H)
    (_hH0 : ∀ t ∈ Icc a b, H (t, 0) = Γ t)
    (_hH1 : ∀ t ∈ Icc a b, H (t, 1) = γ t)
    (_hH_endpoints : ∀ s ∈ Icc (0:ℝ) 1, H (a, s) = 0 ∧ H (b, s) = 0)
    (_hH_nonzero : ∀ t ∈ Ioo a b, ∀ s ∈ Icc (0:ℝ) 1, H (t, s) ≠ 0) :
    generalizedWindingNumber Γ a b 0 = generalizedWindingNumber γ a b 0

- theorem zeppelinCurve_windingNumber :
    generalizedWindingNumber zeppelinCurve 0 (2 * Real.pi) 0 = 3/2

- theorem generalizedWindingNumber_eq_classical
    (γ : PiecewiseC1Curve') (_hclosed : γ.IsClosed) (z₀ : ℂ)
    (_hoff : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ z₀) :
    generalizedWindingNumber γ.toFun γ.a γ.b z₀ ∈ Set.range (fun n : ℤ => (n : ℂ))

- theorem valenceFormula
    (k : ℤ) (f : ModularForm Γ(1) k)
    (_hf_nonzero : f ≠ 0)
    -- The set of zeros in the fundamental domain (excluding elliptic points)
    (S : Finset UpperHalfPlane)
    (_hS : ∀ p ∈ S, (p : ℂ) ∈ fundamentalDomain ∧ p ≠ ellipticPoint_i ∧ p ≠ ellipticPoint_rho) :
    (orderAtCusp f : ℚ) +
    (1/2 : ℚ) * orderOfVanishingAt f ellipticPoint_i +
    (1/3 : ℚ) * orderOfVanishingAt f ellipticPoint_rho +
    ∑ p ∈ S, (orderOfVanishingAt f p : ℚ) = k / 12

- theorem valenceFormula_neg_weight (k : ℤ) (hk : k < 0) (f : ModularForm Γ(1) k) :
    f = 0

- theorem valenceFormula_weight_zero_constant (f : ModularForm Γ(1) 0) :
    ∃ c : ℂ, ∀ z : UpperHalfPlane, f z = c

- theorem delta_zeros (Δ : ModularForm Γ(1) 12) (_hΔ : Δ ≠ 0) :
    orderAtCusp Δ = 1 ∧
    orderOfVanishingAt Δ ellipticPoint_i = 0 ∧
    orderOfVanishingAt Δ ellipticPoint_rho = 0 ∧
    ∀ z : UpperHalfPlane, (z : ℂ) ∈ fundamentalDomain → z ≠ ellipticPoint_i → z ≠ ellipticPoint_rho →
      orderOfVanishingAt Δ z = 0

The following was negated by Aristotle:

- theorem piecewiseC1_flat_order_one (γ : PiecewiseC1Curve') (t : ℝ) :
    FlatOfOrder γ.toFun t 1

Here is the code for the `negate_state` tactic, used within these negations:

```lean
import Mathlib
open Lean Meta Elab Tactic in
elab "revert_all" : tactic => do
  let goals ← getGoals
  let mut newGoals : List MVarId := []
  for mvarId in goals do
    newGoals := newGoals.append [(← mvarId.revertAll)]
  setGoals newGoals

open Lean.Elab.Tactic in
macro "negate_state" : tactic => `(tactic|
  (
    guard_goal_nums 1
    revert_all
    refine @(((by admit) : ∀ {p : Prop}, ¬p → p) ?_)
    try (push_neg; guard_goal_nums 1)
  )
)
```



At Harmonic, we use a modified version of the `generalize_proofs` tactic.
For compatibility, we include this tactic at the start of the file.
If you add the comment "-- Harmonic `generalize_proofs` tactic" to your file, we will not do this.
-/

/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Your Name]

# Generalized Residue Theorem

This file formalizes the generalized residue theorem from
"Non-integer valued winding numbers and a generalized Residue Theorem"
by Hungerbuehler and Wasem.

## Main definitions

* `ModelSectorCurve`: A curve consisting of a straight line from 0 to r,
  an arc of angle α, and a straight line back to 0.
* `GeneralizedWindingNumber`: The winding number defined via Cauchy principal value,
  which can be non-integer for points on the curve.
* `FlatOfOrder`: A curve is flat of order n at a point if it deviates from the tangent
  by o(|z - z₀|ⁿ).

## Main results

* `generalizedWindingNumber_modelSector`: For a model sector curve with angle α,
  the winding number at 0 is α/(2π).
* `generalizedWindingNumber_bounded_integrand`: The real version of the winding number
  has a bounded integrand.
* `generalizedResidueTheorem`: The residue theorem extended to allow singularities
  on the contour (with appropriate conditions).

## References

* Hungerbuehler, Wasem: "Non-integer valued winding numbers and a generalized Residue Theorem"
-/


import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.NumberTheory.Modular
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.RingTheory.LaurentSeries
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.QExpansion


import Mathlib.Tactic.GeneralizeProofs
/-
namespace Harmonic.GeneralizeProofs
-- Harmonic `generalize_proofs` tactic

open Lean Meta Elab Parser.Tactic Elab.Tactic Mathlib.Tactic.GeneralizeProofs
def mkLambdaFVarsUsedOnly' (fvars : Array Expr) (e : Expr) : MetaM (Array Expr × Expr) := do
  let mut e := e
  let mut fvars' : List Expr := []
  for i' in [0:fvars.size] do
    let fvar := fvars[fvars.size - i' - 1]!
    e ← mkLambdaFVars #[fvar] e (usedOnly := false) (usedLetOnly := false)
    match e with
    | .letE _ _ v b _ => e := b.instantiate1 v
    | .lam _ _ _b _ => fvars' := fvar :: fvars'
    | _ => unreachable!
  return (fvars'.toArray, e)

partial def abstractProofs' (e : Expr) (ty? : Option Expr) : MAbs Expr := do
  if (← read).depth ≤ (← read).config.maxDepth then MAbs.withRecurse <| visit (← instantiateMVars e) ty?
  else return e
where
  visit (e : Expr) (ty? : Option Expr) : MAbs Expr := do
    if (← read).config.debug then
      if let some ty := ty? then
        unless ← isDefEq (← inferType e) ty do
          throwError "visit: type of{indentD e}\nis not{indentD ty}"
    if e.isAtomic then
      return e
    else
      checkCache (e, ty?) fun _ ↦ do
        if ← isProof e then
          visitProof e ty?
        else
          match e with
          | .forallE n t b i =>
            withLocalDecl n i (← visit t none) fun x ↦ MAbs.withLocal x do
              mkForallFVars #[x] (← visit (b.instantiate1 x) none) (usedOnly := false) (usedLetOnly := false)
          | .lam n t b i => do
            withLocalDecl n i (← visit t none) fun x ↦ MAbs.withLocal x do
              let ty'? ←
                if let some ty := ty? then
                  let .forallE _ _ tyB _ ← pure ty
                    | throwError "Expecting forall in abstractProofs .lam"
                  pure <| some <| tyB.instantiate1 x
                else
                  pure none
              mkLambdaFVars #[x] (← visit (b.instantiate1 x) ty'?) (usedOnly := false) (usedLetOnly := false)
          | .letE n t v b _ =>
            let t' ← visit t none
            withLetDecl n t' (← visit v t') fun x ↦ MAbs.withLocal x do
              mkLetFVars #[x] (← visit (b.instantiate1 x) ty?) (usedLetOnly := false)
          | .app .. =>
            e.withApp fun f args ↦ do
              let f' ← visit f none
              let argTys ← appArgExpectedTypes f' args ty?
              let mut args' := #[]
              for arg in args, argTy in argTys do
                args' := args'.push <| ← visit arg argTy
              return mkAppN f' args'
          | .mdata _ b  => return e.updateMData! (← visit b ty?)
          | .proj _ _ b => return e.updateProj! (← visit b none)
          | _           => unreachable!
  visitProof (e : Expr) (ty? : Option Expr) : MAbs Expr := do
    let eOrig := e
    let fvars := (← read).fvars
    let e := e.withApp' fun f args => f.beta args
    if e.withApp' fun f args => f.isAtomic && args.all fvars.contains then return e
    let e ←
      if let some ty := ty? then
        if (← read).config.debug then
          unless ← isDefEq ty (← inferType e) do
            throwError m!"visitProof: incorrectly propagated type{indentD ty}\nfor{indentD e}"
        mkExpectedTypeHint e ty
      else pure e
    if (← read).config.debug then
      unless ← Lean.MetavarContext.isWellFormed (← getLCtx) e do
        throwError m!"visitProof: proof{indentD e}\nis not well-formed in the current context\n\
          fvars: {fvars}"
    let (fvars', pf) ← mkLambdaFVarsUsedOnly' fvars e
    if !(← read).config.abstract && !fvars'.isEmpty then
      return eOrig
    if (← read).config.debug then
      unless ← Lean.MetavarContext.isWellFormed (← read).initLCtx pf do
        throwError m!"visitProof: proof{indentD pf}\nis not well-formed in the initial context\n\
          fvars: {fvars}\n{(← mkFreshExprMVar none).mvarId!}"
    let pfTy ← instantiateMVars (← inferType pf)
    let pfTy ← abstractProofs' pfTy none
    if let some pf' ← MAbs.findProof? pfTy then
      return mkAppN pf' fvars'
    MAbs.insertProof pfTy pf
    return mkAppN pf fvars'
partial def withGeneralizedProofs' {α : Type} [Inhabited α] (e : Expr) (ty? : Option Expr)
    (k : Array Expr → Array Expr → Expr → MGen α) :
    MGen α := do
  let propToFVar := (← get).propToFVar
  let (e, generalizations) ← MGen.runMAbs <| abstractProofs' e ty?
  let rec
    go [Inhabited α] (i : Nat) (fvars pfs : Array Expr)
        (proofToFVar propToFVar : ExprMap Expr) : MGen α := do
      if h : i < generalizations.size then
        let (ty, pf) := generalizations[i]
        let ty := (← instantiateMVars (ty.replace proofToFVar.get?)).cleanupAnnotations
        withLocalDeclD (← mkFreshUserName `pf) ty fun fvar => do
          go (i + 1) (fvars := fvars.push fvar) (pfs := pfs.push pf)
            (proofToFVar := proofToFVar.insert pf fvar)
            (propToFVar := propToFVar.insert ty fvar)
      else
        withNewLocalInstances fvars 0 do
          let e' := e.replace proofToFVar.get?
          modify fun s => { s with propToFVar }
          k fvars pfs e'
  go 0 #[] #[] (proofToFVar := {}) (propToFVar := propToFVar)

partial def generalizeProofsCore'
    (g : MVarId) (fvars rfvars : Array FVarId) (target : Bool) :
    MGen (Array Expr × MVarId) := go g 0 #[]
where
  go (g : MVarId) (i : Nat) (hs : Array Expr) : MGen (Array Expr × MVarId) := g.withContext do
    let tag ← g.getTag
    if h : i < rfvars.size then
      let fvar := rfvars[i]
      if fvars.contains fvar then
        let tgt ← instantiateMVars <| ← g.getType
        let ty := (if tgt.isLet then tgt.letType! else tgt.bindingDomain!).cleanupAnnotations
        if ← pure tgt.isLet <&&> Meta.isProp ty then
          let tgt' := Expr.forallE tgt.letName! ty tgt.letBody! .default
          let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
          g.assign <| .app g' tgt.letValue!
          return ← go g'.mvarId! i hs
        if let some pf := (← get).propToFVar.get? ty then
          let tgt' := tgt.bindingBody!.instantiate1 pf
          let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
          g.assign <| .lam tgt.bindingName! tgt.bindingDomain! g' tgt.bindingInfo!
          return ← go g'.mvarId! (i + 1) hs
        match tgt with
        | .forallE n t b bi =>
          let prop ← Meta.isProp t
          withGeneralizedProofs' t none fun hs' pfs' t' => do
            let t' := t'.cleanupAnnotations
            let tgt' := Expr.forallE n t' b bi
            let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
            g.assign <| mkAppN (← mkLambdaFVars hs' g' (usedOnly := false) (usedLetOnly := false)) pfs'
            let (fvar', g') ← g'.mvarId!.intro1P
            g'.withContext do Elab.pushInfoLeaf <|
              .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
            if prop then
              MGen.insertFVar t' (.fvar fvar')
            go g' (i + 1) (hs ++ hs')
        | .letE n t v b _ =>
          withGeneralizedProofs' t none fun hs' pfs' t' => do
            withGeneralizedProofs' v t' fun hs'' pfs'' v' => do
              let tgt' := Expr.letE n t' v' b false
              let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
              g.assign <| mkAppN (← mkLambdaFVars (hs' ++ hs'') g' (usedOnly := false) (usedLetOnly := false)) (pfs' ++ pfs'')
              let (fvar', g') ← g'.mvarId!.intro1P
              g'.withContext do Elab.pushInfoLeaf <|
                .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
              go g' (i + 1) (hs ++ hs' ++ hs'')
        | _ => unreachable!
      else
        let (fvar', g') ← g.intro1P
        g'.withContext do Elab.pushInfoLeaf <|
          .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
        go g' (i + 1) hs
    else if target then
      withGeneralizedProofs' (← g.getType) none fun hs' pfs' ty' => do
        let g' ← mkFreshExprSyntheticOpaqueMVar ty' tag
        g.assign <| mkAppN (← mkLambdaFVars hs' g' (usedOnly := false) (usedLetOnly := false)) pfs'
        return (hs ++ hs', g'.mvarId!)
    else
      return (hs, g)

end GeneralizeProofs

open Lean Elab Parser.Tactic Elab.Tactic Mathlib.Tactic.GeneralizeProofs
partial def generalizeProofs'
    (g : MVarId) (fvars : Array FVarId) (target : Bool) (config : Config := {}) :
    MetaM (Array Expr × MVarId) := do
  let (rfvars, g) ← g.revert fvars (clearAuxDeclsInsteadOfRevert := true)
  g.withContext do
    let s := { propToFVar := ← initialPropToFVar }
    GeneralizeProofs.generalizeProofsCore' g fvars rfvars target |>.run config |>.run' s

elab (name := generalizeProofsElab'') "generalize_proofs" config?:(Parser.Tactic.config)?
    hs:(ppSpace colGt binderIdent)* loc?:(location)? : tactic => withMainContext do
  let config ← elabConfig (mkOptionalNode config?)
  let (fvars, target) ←
    match expandOptLocation (Lean.mkOptionalNode loc?) with
    | .wildcard => pure ((← getLCtx).getFVarIds, true)
    | .targets t target => pure (← getFVarIds t, target)
  liftMetaTactic1 fun g => do
    let (pfs, g) ← generalizeProofs' g fvars target config
    g.withContext do
      let mut lctx ← getLCtx
      for h in hs, fvar in pfs do
        if let `(binderIdent| $s:ident) := h then
          lctx := lctx.setUserName fvar.fvarId! s.getId
        Expr.addLocalVarInfoForBinderIdent fvar h
      Meta.withLCtx lctx (← Meta.getLocalInstances) do
        let g' ← Meta.mkFreshExprSyntheticOpaqueMVar (← g.getType) (← g.getTag)
        g.assign g'
        return g'.mvarId!

 end Harmonic
 -/

open Complex Set Filter Function MeasureTheory TopologicalSpace Metric Asymptotics HahnSeries

open scoped Real Topology BigOperators Nat Interval Modular CongruenceSubgroup

noncomputable section

/-! ## Piecewise C¹ curves and cycles -/

/-- A piecewise C¹ curve is a continuous curve that is C¹ on each piece of a finite partition. -/
structure PiecewiseC1Curve' where
  /-- The underlying continuous function -/
  toFun : ℝ → ℂ
  /-- The domain of definition -/
  a : ℝ
  b : ℝ
  hab : a < b
  /-- Continuity on the domain -/
  continuous_toFun : ContinuousOn toFun (Icc a b)
  /-- Partition points where the curve may fail to be differentiable -/
  partition : Finset ℝ
  /-- Partition is contained in the domain -/
  partition_subset : ↑partition ⊆ Icc a b
  /-- The curve is C¹ on each open interval of the partition -/
  differentiable_on_partition :
    ∀ t ∈ Icc a b, t ∉ partition → DifferentiableAt ℝ toFun t

instance : CoeFun PiecewiseC1Curve' (fun _ => ℝ → ℂ) where
  coe := PiecewiseC1Curve'.toFun

/-- A piecewise C¹ curve is closed if γ(a) = γ(b) -/
def PiecewiseC1Curve'.IsClosed (γ : PiecewiseC1Curve') : Prop :=
  γ.toFun γ.a = γ.toFun γ.b

/-- A piecewise C¹ immersion is a piecewise C¹ curve with nonzero derivative -/
structure PiecewiseC1Immersion' extends PiecewiseC1Curve' where
  /-- The derivative is nonzero away from partition points -/
  deriv_ne_zero : ∀ t ∈ Icc toPiecewiseC1Curve'.a toPiecewiseC1Curve'.b,
    t ∉ toPiecewiseC1Curve'.partition →
    deriv toPiecewiseC1Curve'.toFun t ≠ 0

/-- A cycle is a formal ℤ-linear combination of closed piecewise C¹ curves. -/
structure Cycle' where
  /-- The curves in the cycle -/
  curves : List PiecewiseC1Curve'
  /-- The multiplicities -/
  multiplicities : List ℤ
  /-- Same length -/
  length_eq : curves.length = multiplicities.length
  /-- All curves are closed -/
  all_closed : ∀ γ ∈ curves, γ.IsClosed

/-! ## Model sector curve -/

/-- The model sector curve: straight line [0,r], arc of angle α, straight line back to 0.
    This is the fundamental building block for analyzing winding numbers at boundary points. -/
structure ModelSectorCurve where
  /-- The radius -/
  r : ℝ
  hr : 0 < r
  /-- The angle in [0, 2π] -/
  α : ℝ
  hα_nonneg : 0 ≤ α
  hα_le : α ≤ 2 * Real.pi

/-- The first segment γ₁: [0,r] → ℂ, t ↦ t (the positive real axis) -/
def ModelSectorCurve.γ₁ (_C : ModelSectorCurve) : ℝ → ℂ :=
  fun t => t

/-- The arc segment γ₂: [0,α] → ℂ, t ↦ r·e^{it} -/
def ModelSectorCurve.γ₂ (C : ModelSectorCurve) : ℝ → ℂ :=
  fun t => C.r * Complex.exp (Complex.I * t)

/-- The third segment γ₃: [0,r] → ℂ, t ↦ (r-t)·e^{iα} -/
def ModelSectorCurve.γ₃ (C : ModelSectorCurve) : ℝ → ℂ :=
  fun t => (C.r - t) * Complex.exp (Complex.I * C.α)

/-! ## Cauchy Principal Value -/

/-- Cauchy principal value of an integral, where we exclude an ε-neighborhood of a point. -/
def cauchyPrincipalValue (f : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) : ℂ :=
  limUnder (𝓝[>] (0 : ℝ)) fun ε =>
    ∫ t in a..b, if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0

/-- The Cauchy principal value exists if the limit converges. -/
def CauchyPrincipalValueExists (f : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) : Prop :=
  ∃ L : ℂ, Tendsto (fun ε =>
    ∫ t in a..b, if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0)
    (𝓝[>] (0 : ℝ)) (𝓝 L)

/-! ## Generalized Winding Number -/

/-- The generalized winding number of a piecewise C¹ cycle with respect to a point z₀,
    defined via the Cauchy principal value. This allows z₀ to lie on the curve itself.

    Definition 2.1 in the paper:
    n_{z₀}(C) := PV (1/(2πi)) ∮_C dz/(z - z₀)
                = lim_{ε→0} (1/(2πi)) ∫_{|C - z₀| > ε} dz/(z - z₀)
-/
def generalizedWindingNumber (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) : ℂ :=
  (2 * Real.pi * Complex.I)⁻¹ * cauchyPrincipalValue (fun z => (z - z₀)⁻¹) γ a b z₀

/-! ## Key computation: winding number of model sector curve -/

/- Aristotle failed to find a proof. -/
/-- The winding number of a model sector curve at the origin equals α/(2π).
    This is the key computation that shows the generalized winding number
    has geometric meaning.

    From Section 2:
    PV ∮_γ dz/z = i·α, hence n₀(γ) = α/(2π)
-/

-- Integral of 1/z along γ₁ (positive real axis from ε to r). -/
lemma integral_gamma1 (r ε : ℝ) (hr : 0 < r) (hε : 0 < ε) (_hεr : ε < r) :
    ∫ t in ε..r, (t : ℂ)⁻¹ = Complex.log r - Complex.log ε := by
  -- Rewrite (t : ℂ)⁻¹ as (t⁻¹ : ℂ) using ofReal_inv
  simp_rw [← Complex.ofReal_inv]
  -- Convert complex integral to real integral
  rw [intervalIntegral.integral_ofReal]
  -- Compute the real integral: ∫_ε^r t⁻¹ dt = log(r/ε)
  rw [integral_inv_of_pos hε hr]
  -- log(r/ε) = log(r) - log(ε)
  rw [Real.log_div hr.ne' hε.ne']
  -- Convert back to complex: (log r - log ε : ℂ) = Complex.log r - Complex.log ε
  simp only [Complex.ofReal_sub]
  rw [Complex.ofReal_log hr.le, Complex.ofReal_log hε.le]

/-- Integral of 1/z along γ₂ (arc of angle α at radius r).
    Since z = r·e^{it}, we have dz = r·i·e^{it} dt and dz/z = i dt. -/
lemma integral_gamma2 (C : ModelSectorCurve) :
    ∫ t in (0 : ℝ)..C.α, Complex.I = Complex.I * C.α := by
  rw [intervalIntegral.integral_const]
  simp only [sub_zero, Complex.real_smul]
  ring

/-- Integral of 1/z along γ₃ (line from r·e^{iα} back to 0, from 0 to r-ε).
    The parametrization is (r-t)·e^{iα}, so dz = -e^{iα} dt and
    dz/z = -dt/(r-t), giving ∫_0^{r-ε} -dt/(r-t) = ln(ε) - ln(r). -/
lemma integral_gamma3 (r ε α : ℝ) (hr : 0 < r) (hε : 0 < ε) (hεr : ε < r) :
    ∫ t in (0 : ℝ)..(r - ε), -((r - t) : ℂ)⁻¹ = Complex.log ε - Complex.log r := by
  -- Pull out the negative: ∫ -f = -∫ f
  rw [intervalIntegral.integral_neg]
  -- Substitution u = r - t: ∫_0^{r-ε} f(r-t) dt = ∫_ε^r f(u) du
  have hsub : ∫ t in (0 : ℝ)..(r - ε), ((r - t) : ℂ)⁻¹ = ∫ u in ε..r, (u : ℂ)⁻¹ := by
    have h := intervalIntegral.integral_comp_sub_left (fun x : ℝ => (x : ℂ)⁻¹) r (a := (0 : ℝ)) (b := r - ε)
    simp only [sub_zero, sub_sub_cancel] at h
    simp only [← Complex.ofReal_sub] at h ⊢
    exact h
  rw [hsub, integral_gamma1 r ε hr hε hεr]
  ring

/-- The cancellation of singular terms: (ln r - ln ε) + (ln ε - ln r) = 0. -/
lemma log_cancellation (r ε : ℝ) (_hr : 0 < r) (_hε : 0 < ε) :
    (Complex.log r - Complex.log ε) + (Complex.log ε - Complex.log r) = 0 := by
  abel



theorem generalizedWindingNumber_modelSector2 (C : ModelSectorCurve) :
    ∃ L : ℂ, Tendsto (fun ε : ℝ =>
      (2 * Real.pi * Complex.I)⁻¹ * ((∫ t in ε..C.r, (t : ℂ)⁻¹) +
        (∫ t in (0 : ℝ)..C.α, Complex.I) +
        (∫ t in (0 : ℝ)..(C.r - ε), -((C.r - t) : ℂ)⁻¹)))
      (𝓝[>] 0) (𝓝 L) ∧ L = C.α / (2 * Real.pi) := by
  -- The proof follows from the three integral lemmas above:
  -- As ε → 0⁺, the sum becomes (ln r - ln ε) + iα + (ln ε - ln r) = iα
  -- Then n₀(γ) = (2πi)⁻¹ · iα = α/(2π)
  use C.α / (2 * Real.pi)
  constructor
  · -- The integral sum simplifies to I * α for small ε, then (2πi)⁻¹ * i*α = α/(2π)
    -- For ε ∈ (0, r), using integral_gamma1 and integral_gamma3:
    -- sum = (log r - log ε) + I*α + (log ε - log r) = I*α
    -- So (2πi)⁻¹ * (I*α) = α/(2π)
    -- The limit is therefore constant on (0, r), hence converges
    refine Tendsto.congr' ?_ tendsto_const_nhds
    -- Show the integral expression eventually equals the constant C.α / (2 * Real.pi)
    filter_upwards [Ioo_mem_nhdsGT C.hr] with ε hε
    -- hε : ε ∈ Ioo 0 C.r, so 0 < ε and ε < C.r
    have hε_pos : 0 < ε := hε.1
    have hε_lt : ε < C.r := hε.2
    -- Compute the three integrals
    have h1 : ∫ t in ε..C.r, (t : ℂ)⁻¹ = Complex.log C.r - Complex.log ε :=
      integral_gamma1 C.r ε C.hr hε_pos hε_lt
    have h2 : ∫ t in (0 : ℝ)..C.α, Complex.I = (C.α - 0) • Complex.I :=
      intervalIntegral.integral_const Complex.I
    have h3 : ∫ t in (0 : ℝ)..(C.r - ε), -((C.r - t) : ℂ)⁻¹ = Complex.log ε - Complex.log C.r :=
      integral_gamma3 C.r ε C.α C.hr hε_pos hε_lt
    -- The goal is: C.α / (2 * π) = (2πi)⁻¹ * ((∫₁) + (∫₂) + (∫₃))
    -- Now with fixed parenthesization in the theorem statement
    --
    -- Compute the sum of integrals: logs cancel, leaving I * α
    have h2' : ∫ t in (0 : ℝ)..C.α, Complex.I = C.α * Complex.I := by
      rw [h2]; simp only [sub_zero, Complex.real_smul]
    -- Prove the sum equals I * α by rewriting each integral
    have sum_eq : (∫ t in ε..C.r, (t : ℂ)⁻¹) + (∫ t in (0 : ℝ)..C.α, Complex.I) +
                  (∫ t in (0 : ℝ)..(C.r - ε), -((C.r - t) : ℂ)⁻¹) = Complex.I * C.α := by
      rw [h1, h2', h3]
      ring
    -- Now apply and simplify
    rw [sum_eq]
    field_simp [Complex.I_ne_zero, Real.pi_ne_zero]
  · rfl

theorem generalizedWindingNumber_modelSector (C : ModelSectorCurve) :
    ∃ L : ℂ, Tendsto (fun ε : ℝ =>
      (2 * Real.pi * Complex.I)⁻¹ * (
        ∫ t in ε..C.r, (t : ℂ)⁻¹ +
        ∫ t in (0 : ℝ)..C.α, Complex.I +
        ∫ t in (0 : ℝ)..(C.r - ε), -((C.r - t) : ℂ)⁻¹))
      (𝓝[>] 0) (𝓝 L) ∧ L = C.α / (2 * Real.pi) := by
  have := generalizedWindingNumber_modelSector2 C
  obtain ⟨L, hL⟩ := this
  use L
  constructor
  convert hL.1 using 2
  done
  apply hL.2
