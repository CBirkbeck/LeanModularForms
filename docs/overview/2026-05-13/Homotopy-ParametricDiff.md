# Inventory: ParametricDiff.lean

File: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/GeneralizedResidueTheory/Homotopy/ParametricDiff.lean`
Lines: 471

### `instance ContinuousSMul ℝ ℂ` (anonymous)
- **Type**: `ContinuousSMul ℝ ℂ`
- **What**: Continuity of the real-scalar action on complex numbers
- **How**: rewrites `r • z = (r : ℂ) * z` and chains continuity of `ofReal` with multiplication
- **Hypotheses**: none
- **Uses from project**: []
- **Used by**: implicit in subsequent `smul`/integration steps
- **Visibility**: private noncomputable instance
- **Lines**: 35-38
- **Notes**: private instance to avoid global typeclass conflicts

### `theorem intervalIntegral_continuous_on_param`
- **Type**: `(f : ℝ → ℝ → ℂ) (a b : ℝ) (S : Set ℝ) (hab : a ≤ b) (hf_cont : Continuous ...) (_hf_int : ...) : ContinuousOn (fun s => ∫ t in a..b, f t s) S`
- **What**: A parametric interval integral is continuous in the parameter `s` when the integrand is jointly continuous
- **How**: `intervalIntegral.continuousAt_of_dominated_interval` with uniform bound `M` from compactness of `Icc a b ×ˢ Icc (s₀-1) (s₀+1)` via `IsCompact.exists_bound_of_continuousOn` (proof >10 lines)
- **Hypotheses**: joint continuity `hf_cont` and pointwise interval integrability (unused parameter)
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 41-68
- **Notes**: >10 lines; the `_hf_int` argument is unused (underscore prefix)

### `lemma contDiff_partialDeriv_snd_of_contDiff_two`
- **Type**: `(H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ 2 H) : ContDiff ℝ 1 (fun p => deriv (fun s => H (p.1, s)) p.2)`
- **What**: For `C²` `H`, the partial derivative in the second variable is `C¹` jointly
- **How**: rewrites `deriv (fun s => H(p.1, s)) p.2 = fderiv ℝ H p (0, 1)` using `fderiv_comp_deriv` for the inclusion `s ↦ (p.1, s)`, then uses `hH.fderiv_right` and `clm_apply`
- **Hypotheses**: `H` is `C²`
- **Uses from project**: []
- **Used by**: `homotopy_partialS_differentiableAt_t`, `homotopy_J_deriv_continuousOn`, `homotopy_F'_continuous`
- **Visibility**: public (no modifier)
- **Lines**: 70-85
- **Notes**: >10 lines

### `lemma contDiff_partialDeriv_fst_of_contDiff_two`
- **Type**: `(H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ 2 H) : ContDiff ℝ 1 (fun p => deriv (fun t => H (t, p.2)) p.1)`
- **What**: For `C²` `H`, the partial derivative in the first variable is `C¹` jointly
- **How**: analogous to `_snd_` version: rewrites partial as `fderiv ℝ H p (1, 0)` via `fderiv_comp_deriv`, then `clm_apply` with `hH.fderiv_right`
- **Hypotheses**: `H` is `C²`
- **Uses from project**: []
- **Used by**: `homotopy_partialT_differentiableAt_s`, `homotopy_mixed_partial_continuous`, `homotopy_F'_continuous`, `homotopy_J_deriv_continuousOn`
- **Visibility**: public
- **Lines**: 87-102
- **Notes**: >10 lines

### `lemma schwarz_partialDeriv_comm`
- **Type**: `(H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ 2 H) (t s : ℝ) : deriv (fun s' => deriv (fun t' => H (t', s')) t) s = deriv (fun t' => deriv (fun s' => H (t', s')) s) t`
- **What**: Schwarz theorem: mixed partials of a `C²` function commute
- **How**: uses `hH.contDiffAt.isSymmSndFDerivAt` to get symmetry; converts both sides via `fderiv_comp_deriv` to `(fderiv ℝ (fderiv H) (t,s)) e₁ e₂` for `e₁, e₂ ∈ {(1,0), (0,1)}`, then concludes by `h_symm.eq` (proof >10 lines)
- **Hypotheses**: `H` is `C²`
- **Uses from project**: []
- **Used by**: `homotopy_schwarz_product_rule`
- **Visibility**: public
- **Lines**: 105-165
- **Notes**: >10 lines

### `private lemma homotopy_H_differentiableAt_s`
- **Type**: `(H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ 2 H) (t s : ℝ) : DifferentiableAt ℝ (fun s' => H (t, s')) s`
- **What**: `s' ↦ H(t, s')` is differentiable when `H` is `C²`
- **How**: composition of total differentiability `hH.differentiable two_ne_zero` with constant-prod inclusion
- **Hypotheses**: `H` is `C²`
- **Uses from project**: []
- **Used by**: `homotopy_fH_differentiableAt_s`, `homotopy_chain_rule_s`
- **Visibility**: private
- **Lines**: 170-173

### `private lemma homotopy_H_differentiableAt_t`
- **Type**: `(H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ 2 H) (t s : ℝ) : DifferentiableAt ℝ (fun t' => H (t', s)) t`
- **What**: `t' ↦ H(t', s)` is differentiable when `H` is `C²`
- **How**: composition of total differentiability with id-prod-const inclusion
- **Hypotheses**: `H` is `C²`
- **Uses from project**: []
- **Used by**: `homotopy_fH_differentiableAt_t`, `homotopy_chain_rule_t`
- **Visibility**: private
- **Lines**: 176-179

### `private lemma homotopy_fH_differentiableAt_s`
- **Type**: `(f : ℂ → ℂ) (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ 2 H) (t s : ℝ) (hf : DifferentiableAt ℂ f (H (t, s))) : DifferentiableAt ℝ (fun s' => f (H (t, s'))) s`
- **What**: `s' ↦ f(H(t, s'))` is real-differentiable
- **How**: scalar-restriction `hf.restrictScalars ℝ` composed with `homotopy_H_differentiableAt_s`
- **Hypotheses**: `H ∈ C²`; `f` ℂ-differentiable at `H(t,s)`
- **Uses from project**: `homotopy_H_differentiableAt_s`
- **Used by**: `homotopy_schwarz_product_rule`, `homotopy_F'_eq`, `hasDerivAt_homotopy_param`
- **Visibility**: private
- **Lines**: 182-185

### `private lemma homotopy_fH_differentiableAt_t`
- **Type**: `(f : ℂ → ℂ) (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ 2 H) (t s : ℝ) (hf : DifferentiableAt ℂ f (H (t, s))) : DifferentiableAt ℝ (fun t' => f (H (t', s))) t`
- **What**: `t' ↦ f(H(t', s))` is real-differentiable
- **How**: scalar-restriction composed with `homotopy_H_differentiableAt_t`
- **Hypotheses**: `H ∈ C²`; `f` ℂ-differentiable at `H(t,s)`
- **Uses from project**: `homotopy_H_differentiableAt_t`
- **Used by**: `homotopy_schwarz_product_rule`, `homotopy_J_deriv_continuousOn`, `hasDerivAt_homotopy_integral_zero`
- **Visibility**: private
- **Lines**: 188-191

### `private lemma homotopy_partialT_differentiableAt_s`
- **Type**: `(H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ 2 H) (t s : ℝ) : DifferentiableAt ℝ (fun s' => deriv (fun t' => H (t', s')) t) s`
- **What**: `s' ↦ ∂H/∂t(t, s')` is real-differentiable
- **How**: factors as `(fun p => deriv (fun t' => H(t', p.2)) p.1) ∘ (fun s' => (t, s'))`, uses `contDiff_partialDeriv_fst_of_contDiff_two` and chain rule
- **Hypotheses**: `H ∈ C²`
- **Uses from project**: `contDiff_partialDeriv_fst_of_contDiff_two`
- **Used by**: `homotopy_schwarz_product_rule`, `homotopy_F'_eq`, `hasDerivAt_homotopy_param`
- **Visibility**: private
- **Lines**: 194-199

### `private lemma homotopy_partialS_differentiableAt_t`
- **Type**: `(H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ 2 H) (t s : ℝ) : DifferentiableAt ℝ (fun t' => deriv (fun s' => H (t', s')) s) t`
- **What**: `t' ↦ ∂H/∂s(t', s)` is real-differentiable
- **How**: factors as `(fun p => deriv (fun s' => H(p.1, s')) p.2) ∘ (fun t' => (t', s))`, uses `contDiff_partialDeriv_snd_of_contDiff_two`
- **Hypotheses**: `H ∈ C²`
- **Uses from project**: `contDiff_partialDeriv_snd_of_contDiff_two`
- **Used by**: `homotopy_schwarz_product_rule`, `homotopy_J_deriv_continuousOn`, `hasDerivAt_homotopy_integral_zero`
- **Visibility**: private
- **Lines**: 202-207

### `private lemma homotopy_chain_rule_s`
- **Type**: `(f : ℂ → ℂ) (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ 2 H) (t s : ℝ) (hf : Differentiable ℂ f) : deriv (fun s' => f (H (t, s'))) s = deriv f (H (t, s)) * deriv (fun s' => H (t, s')) s`
- **What**: Chain rule for `s' ↦ f(H(t, s'))`
- **How**: `deriv.scomp` of ℂ-differentiable `f` with real-differentiable inner map; rearranges `smul_eq_mul, mul_comm`
- **Hypotheses**: `f` ℂ-differentiable; `H ∈ C²`
- **Uses from project**: `homotopy_H_differentiableAt_s`
- **Used by**: `homotopy_schwarz_product_rule`, `homotopy_F'_eq`
- **Visibility**: private
- **Lines**: 210-215

### `private lemma homotopy_chain_rule_t`
- **Type**: `(f : ℂ → ℂ) (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ 2 H) (t s : ℝ) (hf : Differentiable ℂ f) : deriv (fun t' => f (H (t', s))) t = deriv f (H (t, s)) * deriv (fun t' => H (t', s)) t`
- **What**: Chain rule for `t' ↦ f(H(t', s))`
- **How**: `deriv.scomp` symmetric to `_s` version
- **Hypotheses**: `f` ℂ-differentiable; `H ∈ C²`
- **Uses from project**: `homotopy_H_differentiableAt_t`
- **Used by**: `homotopy_schwarz_product_rule`, `homotopy_J_deriv_continuousOn`
- **Visibility**: private
- **Lines**: 218-223

### `private lemma homotopy_schwarz_product_rule`
- **Type**: `(f : ℂ → ℂ) (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ 2 H) (t s : ℝ) (hf_at : DifferentiableAt ...) (hf : Differentiable ℂ f) : deriv (fun s' => f (H (t, s')) * deriv (fun t' => H (t', s')) t) s = deriv (fun t' => f (H (t', s)) * deriv (fun s'' => H (t', s'')) s) t`
- **What**: The s-derivative of `f(H)·∂H/∂t` equals the t-derivative of `f(H)·∂H/∂s` via product+chain+Schwarz
- **How**: applies `deriv_mul` on both sides, then chain rule `homotopy_chain_rule_s/t` and Schwarz `schwarz_partialDeriv_comm`, finishes with `ring` (proof >10 lines)
- **Hypotheses**: `H ∈ C²`; `f` differentiable
- **Uses from project**: `homotopy_fH_differentiableAt_s`, `homotopy_partialT_differentiableAt_s`, `homotopy_fH_differentiableAt_t`, `homotopy_partialS_differentiableAt_t`, `homotopy_chain_rule_s`, `homotopy_chain_rule_t`, `schwarz_partialDeriv_comm`
- **Used by**: `hasDerivAt_homotopy_param`, `hasDerivAt_homotopy_integral_zero`
- **Visibility**: private
- **Lines**: 227-247
- **Notes**: >10 lines

### `private lemma homotopy_mixed_partial_continuous`
- **Type**: `(H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ 2 H) : Continuous (fun p => deriv (fun s' => deriv (fun t' => H (t', s')) p.1) p.2)`
- **What**: Continuity of mixed partial `(t, s') ↦ ∂/∂s' ∂H/∂t`
- **How**: rewrites mixed partial as `fderiv (fun p => ∂H/∂t(p.1, p.2)) (p) (0,1)` via `fderiv_comp_deriv`, then applies `clm_apply` with `h_partialT.continuous_fderiv` (proof >10 lines)
- **Hypotheses**: `H ∈ C²`
- **Uses from project**: `contDiff_partialDeriv_fst_of_contDiff_two`
- **Used by**: `homotopy_F'_continuous`
- **Visibility**: private
- **Lines**: 252-274
- **Notes**: >10 lines

### `private lemma homotopy_F'_eq`
- **Type**: `(f : ℂ → ℂ) (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ 2 H) (hf : Differentiable ℂ f) (t s' : ℝ) : deriv (fun s'' => f (H (t, s'')) * deriv (fun t' => H (t', s'')) t) s' = deriv f (H (t, s')) * deriv (fun s'' => H (t, s'')) s' * deriv (fun t' => H (t', s')) t + f (H (t, s')) * deriv (fun s'' => deriv (fun t' => H (t', s'')) t) s'`
- **What**: Closed-form for the s-derivative of `f(H(t,·)) * ∂H/∂t(t,·)`
- **How**: product rule `deriv_mul` together with chain rule `homotopy_chain_rule_s`, then `mul_assoc; rfl` via `erw` (proof >10 lines)
- **Hypotheses**: `H ∈ C²`; `f` differentiable
- **Uses from project**: `homotopy_fH_differentiableAt_s`, `homotopy_chain_rule_s`, `homotopy_partialT_differentiableAt_s`
- **Used by**: `homotopy_F'_continuous`
- **Visibility**: private
- **Lines**: 277-290
- **Notes**: uses `erw`

### `private lemma homotopy_F'_continuous`
- **Type**: `(f : ℂ → ℂ) (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ 2 H) (hfH_cont : Continuous (f ∘ H)) (hf : Differentiable ℂ f) : Continuous (fun p => deriv (fun s'' => f (H (p.1, s'')) * deriv (fun t' => H (t', s'')) p.1) p.2)`
- **What**: Joint continuity of `(t, s') ↦ ∂/∂s' [f(H)·∂H/∂t]`
- **How**: substitutes the closed form `homotopy_F'_eq`; continuity of each summand from `contDiff_partialDeriv_*` lemmas, `hf.contDiff |>.continuous_deriv` composed with `hH.continuous`, plus `homotopy_mixed_partial_continuous` (proof >10 lines)
- **Hypotheses**: `H ∈ C²`; `f ∘ H` continuous; `f` differentiable
- **Uses from project**: `contDiff_partialDeriv_fst_of_contDiff_two`, `contDiff_partialDeriv_snd_of_contDiff_two`, `homotopy_F'_eq`, `homotopy_mixed_partial_continuous`
- **Used by**: `homotopy_uniform_bound`, `hasDerivAt_homotopy_param`
- **Visibility**: private
- **Lines**: 293-311
- **Notes**: >10 lines

### `private lemma homotopy_uniform_bound`
- **Type**: `(f : ℂ → ℂ) (H : ℝ × ℝ → ℂ) (a b s : ℝ) (hab : a < b) (hH : ContDiff ℝ 2 H) (hfH_cont : Continuous (f ∘ H)) (hf : Differentiable ℂ f) : ∃ ε M, 0 < ε ∧ (uniform bound on s'-derivative) ∧ IntervalIntegrable (const M) ∧ ball s ε ∈ 𝓝 s`
- **What**: Uniform `M`-bound on the s'-derivative of `f(H)·∂H/∂t` over `Icc a b × Icc (s-ε) (s+ε)`
- **How**: takes `ε = 1/4`; `IsCompact.exists_isMaxOn` on the compact product to get max-point `M_pt`; bound applies pointwise via `hM_pt_max` after subsetting `ball s ε ⊆ Icc(s-ε, s+ε)` (proof >10 lines)
- **Hypotheses**: `a < b`; `H ∈ C²`; `f∘H` continuous; `f` differentiable
- **Uses from project**: `homotopy_F'_continuous`
- **Used by**: `hasDerivAt_homotopy_param`
- **Visibility**: private
- **Lines**: 314-342
- **Notes**: >10 lines

### `private lemma homotopy_F_continuous_t`
- **Type**: `(f : ℂ → ℂ) (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ 2 H) (hfH_cont : Continuous (f ∘ H)) (s' : ℝ) : Continuous (fun t => f (H (t, s')) * deriv (fun t' => H (t', s')) t)`
- **What**: `t ↦ f(H(t, s'))·∂H/∂t(t, s')` is continuous for fixed `s'`
- **How**: composes `hfH_cont` and `contDiff_partialDeriv_fst_of_contDiff_two.continuous` along the inclusion `t ↦ (t, s')`, then `.mul`
- **Hypotheses**: `H ∈ C²`; `f∘H` continuous
- **Uses from project**: `contDiff_partialDeriv_fst_of_contDiff_two`
- **Used by**: `hasDerivAt_homotopy_param`
- **Visibility**: private
- **Lines**: 345-350

### `private lemma hasDerivAt_homotopy_param`
- **Type**: `(f : ℂ → ℂ) (H : ℝ × ℝ → ℂ) (a b s : ℝ) (hab : a < b) (hH_smooth : ContDiff ℝ 2 H) (hf_diff hfH_cont hs hf_differentiable h_schwarz) : HasDerivAt (fun s' => ∫ t in a..b, f (H (t, s'))·∂H/∂t) (∫ t in a..b, ∂/∂t [f(H(t', s))·∂H/∂s]) s`
- **What**: Derivative of the parametric integral in `s` equals the integral of the t-derivative (via Schwarz)
- **How**: `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le` applied with the uniform bound from `homotopy_uniform_bound`; rewrites the integrand via `h_schwarz` and `homotopy_schwarz_product_rule` (proof >10 lines)
- **Hypotheses**: `a < b`; `H ∈ C²`; `f` ℂ-differentiable on path; Schwarz identity off boundary
- **Uses from project**: `homotopy_F_continuous_t`, `homotopy_F'_continuous`, `homotopy_uniform_bound`, `homotopy_fH_differentiableAt_s`, `homotopy_partialT_differentiableAt_s`, `homotopy_schwarz_product_rule`
- **Used by**: `hasDerivAt_homotopy_integral_zero`
- **Visibility**: private
- **Lines**: 352-391
- **Notes**: >10 lines

### `private lemma homotopy_J_deriv_continuousOn`
- **Type**: `(f : ℂ → ℂ) (H : ℝ × ℝ → ℂ) (a b s : ℝ) (hH : ContDiff ℝ 2 H) (hfH_cont : Continuous (f ∘ H)) (hf_diff : ...) (hs : s ∈ Icc 0 1) (hf : Differentiable ℂ f) : ContinuousOn (fun t => deriv (fun t' => f (H (t', s)) * ∂H/∂s) t) (Icc a b)`
- **What**: Continuity on `[a,b]` of `t ↦ ∂/∂t [f(H(t,s))·∂H/∂s(t,s)]`
- **How**: product rule `deriv_mul` and chain rule `homotopy_chain_rule_t` make the derivative explicit; continuity of each factor via composition of `contDiff_partialDeriv_*` with the inclusion `t ↦ (t, s)`, then `ContinuousOn.add` (proof >10 lines)
- **Hypotheses**: `H ∈ C²`; `f∘H` continuous; `f` ℂ-differentiable along path
- **Uses from project**: `contDiff_partialDeriv_snd_of_contDiff_two`, `contDiff_partialDeriv_fst_of_contDiff_two`, `homotopy_fH_differentiableAt_t`, `homotopy_partialS_differentiableAt_t`, `homotopy_chain_rule_t`
- **Used by**: `hasDerivAt_homotopy_integral_zero`
- **Visibility**: private
- **Lines**: 396-431
- **Notes**: >10 lines

### `theorem hasDerivAt_homotopy_integral_zero`
- **Type**: `(f : ℂ → ℂ) (H : ℝ × ℝ → ℂ) (a b s : ℝ) (hab : a < b) (hH_smooth : ContDiff ℝ 2 H) (hf_diff hfH_cont hs hderiv_a hderiv_b hf_differentiable) : HasDerivAt (fun s' => ∫ t in a..b, f (H (t, s'))·∂H/∂t) 0 s`
- **What**: The homotopy integral has derivative `0` in `s` when boundary `s`-derivatives `∂H/∂s(a,s)` and `∂H/∂s(b,s)` vanish
- **How**: writes boundary term `J(b,s) - J(a,s) = 0` from `hderiv_a/b`; uses FTC via `intervalIntegral.integral_eq_sub_of_hasDerivAt` for the t-derivative integrand; combines with `hasDerivAt_homotopy_param` and `homotopy_schwarz_product_rule` (proof >10 lines)
- **Hypotheses**: `a < b`; `H ∈ C²`; `f ∘ H` continuous; `f` ℂ-differentiable; boundary `s`-derivatives vanish
- **Uses from project**: `homotopy_fH_differentiableAt_t`, `homotopy_partialS_differentiableAt_t`, `homotopy_J_deriv_continuousOn`, `homotopy_schwarz_product_rule`, `hasDerivAt_homotopy_param`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 434-469
- **Notes**: >10 lines; the public capstone result

## File Summary

ParametricDiff.lean provides the analytical kernel for homotopy invariance of contour integrals. The headline result `hasDerivAt_homotopy_integral_zero` shows that under a `C²` homotopy `H` with vanishing `s`-derivatives at the endpoints `t=a, t=b`, the parametric integral `∫ f(H(t, s)) · ∂H/∂t dt` is constant in `s`. The proof stack: (i) joint smoothness of partial derivatives (`contDiff_partialDeriv_{fst,snd}_of_contDiff_two`); (ii) Schwarz commutativity of mixed partials (`schwarz_partialDeriv_comm`); (iii) a product/chain rule identity matching the `s`-derivative to a `t`-derivative (`homotopy_schwarz_product_rule`); (iv) a uniform bound on the integrand's `s`-derivative for the dominated convergence theorem (`homotopy_uniform_bound`); (v) the parametric Leibniz rule `hasDerivAt_homotopy_param`. Most of the file consists of `private` plumbing lemmas; the only public exports are `intervalIntegral_continuous_on_param`, the two `contDiff_partialDeriv_*` lemmas, `schwarz_partialDeriv_comm`, and the capstone theorem.
