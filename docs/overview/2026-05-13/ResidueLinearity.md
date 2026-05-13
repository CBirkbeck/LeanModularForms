# ResidueLinearity.lean Inventory

Path: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/ResidueLinearity.lean`

---

### theorem `HasSimplePoleAt.add`
- Type: `{f g : ℂ → ℂ} {z₀ : ℂ} (hf : HasSimplePoleAt f z₀) (hg : HasSimplePoleAt g z₀) → HasSimplePoleAt (fun z => f z + g z) z₀`
- What: Closure of simple-pole structure under addition; new coefficient is `hf.coeff + hg.coeff`.
- How: Refines to `⟨hf.coeff + hg.coeff, fun z => hf.regularPart z + hg.regularPart z, hf.regularPart_analyticAt.add hg.regularPart_analyticAt, ?_⟩`; on the witness uses `filter_upwards [hf.eventually_eq, hg.eventually_eq]` and `ring`.
- Hypotheses: `HasSimplePoleAt f z₀`, `HasSimplePoleAt g z₀`.
- Uses-from-project: `HasSimplePoleAt`, `HasSimplePoleAt.coeff`, `HasSimplePoleAt.regularPart`, `HasSimplePoleAt.regularPart_analyticAt`, `HasSimplePoleAt.eventually_eq`.
- Used by: `HasSimplePoleAt.finset_sum`, `residue_finset_sum`.
- Visibility: public.
- Lines: 44-50.

### theorem `HasSimplePoleAt.sub`
- Type: `(hf : HasSimplePoleAt f z₀) (hg : HasSimplePoleAt g z₀) → HasSimplePoleAt (fun z => f z - g z) z₀`
- What: Closure of simple-pole structure under subtraction; new coefficient is `hf.coeff - hg.coeff`.
- How: Mirrors `add`: refines to `⟨hf.coeff - hg.coeff, fun z => hf.regularPart z - hg.regularPart z, ...sub..., ?_⟩`; uses `filter_upwards` + `ring`.
- Hypotheses: same as `add`.
- Uses-from-project: `HasSimplePoleAt`, `HasSimplePoleAt.coeff`, `HasSimplePoleAt.regularPart`, `HasSimplePoleAt.regularPart_analyticAt`, `HasSimplePoleAt.eventually_eq`.
- Used by: external (`residue_sub` direct, not within file).
- Visibility: public.
- Lines: 54-60.

### theorem `HasSimplePoleAt.const_mul`
- Type: `(c : ℂ) (hf : HasSimplePoleAt f z₀) → HasSimplePoleAt (fun z => c * f z) z₀`
- What: Scalar-multiplication closure of simple-pole structure; new coefficient is `c * hf.coeff`.
- How: Refines to `⟨c * hf.coeff, fun z => c * hf.regularPart z, analyticAt_const.mul hf.regularPart_analyticAt, ?_⟩`; `filter_upwards [hf.eventually_eq]`; `ring`.
- Hypotheses: `HasSimplePoleAt f z₀`.
- Uses-from-project: `HasSimplePoleAt.coeff`, `HasSimplePoleAt.regularPart`, `HasSimplePoleAt.regularPart_analyticAt`, `HasSimplePoleAt.eventually_eq`.
- Used by: external.
- Visibility: public.
- Lines: 64-70.

### theorem `HasSimplePoleAt.finset_sum`
- Type: `{ι : Type*} [DecidableEq ι] (s : Finset ι) (F : ι → ℂ → ℂ) (z₀ : ℂ) (hF : ∀ i ∈ s, HasSimplePoleAt (F i) z₀) → HasSimplePoleAt (fun z => ∑ i ∈ s, F i z) z₀`
- What: Finite sum of simple-pole functions is again a simple-pole function.
- How: `Finset.induction`; empty case: `⟨0, fun _ => 0, analyticAt_const, ?_⟩` with `filter_upwards with z; simp`; inductive case: uses `hF i (Finset.mem_insert_self _ _)` and `ih`, then `hi_simple.add hs_simple`; pulls coefficient/regular-part via `h_add.choose` / `h_add.choose_spec`; concludes with `Finset.sum_insert hi_notin`.
- Hypotheses: each summand has a simple pole at `z₀`.
- Uses-from-project: `HasSimplePoleAt.add` (above), `HasSimplePoleAt` constructor, `Finset.sum_insert`.
- Used by: `residue_finset_sum`.
- Visibility: public.
- Lines: 74-91.

### theorem `residue_add`
- Type: `{f g : ℂ → ℂ} {z₀ : ℂ} (hf : HasSimplePoleAt f z₀) (hg : HasSimplePoleAt g z₀) → residue (fun z => f z + g z) z₀ = residue f z₀ + residue g z₀`
- What: Residue of a sum equals the sum of residues, for simple poles.
- How: First establishes `residue (f+g) z₀ = hf.coeff + hg.coeff` via `residue_eq_of_simple_pole_decomp` with witness `z ↦ hf.regularPart z + hg.regularPart z` and `filter_upwards [hf.eventually_eq, hg.eventually_eq]` + `ring`; then `rw [h_eq, residue_eq_coeff hf, residue_eq_coeff hg]`.
- Hypotheses: `HasSimplePoleAt f z₀`, `HasSimplePoleAt g z₀`.
- Uses-from-project: `residue`, `residue_eq_of_simple_pole_decomp`, `residue_eq_coeff`, `HasSimplePoleAt.regularPart_analyticAt`, `HasSimplePoleAt.eventually_eq`.
- Used by: `residue_finset_sum`.
- Visibility: public.
- Lines: 98-109.

### theorem `residue_sub`
- Type: `(hf : HasSimplePoleAt f z₀) (hg : HasSimplePoleAt g z₀) → residue (fun z => f z - g z) z₀ = residue f z₀ - residue g z₀`
- What: Residue of a difference equals the difference of residues.
- How: Same pattern as `residue_add`: `residue_eq_of_simple_pole_decomp` with `g := fun z => hf.regularPart z - hg.regularPart z` and `analyticAt.sub`; `filter_upwards` + `ring`; then `rw [h_eq, residue_eq_coeff hf, residue_eq_coeff hg]`.
- Hypotheses: same.
- Uses-from-project: `residue`, `residue_eq_of_simple_pole_decomp`, `residue_eq_coeff`, `HasSimplePoleAt.eventually_eq`.
- Used by: external.
- Visibility: public.
- Lines: 113-124.

### theorem `residue_const_mul`
- Type: `(c : ℂ) (hf : HasSimplePoleAt f z₀) → residue (fun z => c * f z) z₀ = c * residue f z₀`
- What: Residue is homogeneous under multiplication by a constant.
- How: `residue_eq_of_simple_pole_decomp` with `c := c * hf.coeff`, `g := fun z => c * hf.regularPart z`, `analyticAt_const.mul ...`; `filter_upwards [hf.eventually_eq]`; `ring`; concluded by `rw [h_eq, residue_eq_coeff hf]`.
- Hypotheses: `HasSimplePoleAt f z₀`.
- Uses-from-project: `residue`, `residue_eq_of_simple_pole_decomp`, `residue_eq_coeff`, `HasSimplePoleAt.eventually_eq`.
- Used by: `residue_const_smul` (alias).
- Visibility: public.
- Lines: 127-138.

### theorem `residue_const_smul`
- Type: `(c : ℂ) (hf : HasSimplePoleAt f z₀) → residue (fun z => c * f z) z₀ = c * residue f z₀`
- What: `c • f` alias of `residue_const_mul` for the `smul` reading.
- How: `residue_const_mul c hf`.
- Hypotheses: same.
- Uses-from-project: `residue_const_mul`.
- Used by: external.
- Visibility: public.
- Lines: 141-144.

### theorem `residue_const_div_sub`
- Type: `(c s : ℂ) → residue (fun z => c / (z - s)) s = c`
- What: The residue of `c/(z-s)` at `s` is `c`.
- How: `residue_eq_of_simple_pole_decomp (g := fun _ => 0) analyticAt_const`; on the witness uses `filter_upwards with z; simp`.
- Hypotheses: none.
- Uses-from-project: `residue`, `residue_eq_of_simple_pole_decomp`.
- Used by: external (pole-by-pole residue computation).
- Visibility: public.
- Lines: 147-153.

### theorem `residue_finset_sum`
- Type: `{ι : Type*} [DecidableEq ι] (s : Finset ι) (F : ι → ℂ → ℂ) (z₀ : ℂ) (hF : ∀ i ∈ s, HasSimplePoleAt (F i) z₀) → residue (fun z => ∑ i ∈ s, F i z) z₀ = ∑ i ∈ s, residue (F i) z₀`
- How: `Finset.induction`; empty case: `simp [Finset.sum_empty]; residue_eq_zero_of_analyticAt analyticAt_const`; inductive case: extracts `hi_simple` and `hs_simple := HasSimplePoleAt.finset_sum s F z₀ ...`, applies `ih`, uses `residue_congr` with `filter_upwards with z; simp [Finset.sum_insert hi_notin]` to convert `∑ insert ⇒ F i z + ∑ over s`, then `residue_add hi_simple hs_simple, ih', Finset.sum_insert hi_notin`.
- Hypotheses: each summand has a simple pole at `z₀`.
- Uses-from-project: `residue`, `residue_congr`, `residue_eq_zero_of_analyticAt`, `residue_add`, `HasSimplePoleAt.finset_sum`.
- Used by: external (multi-pole residue applications).
- Visibility: public.
- Lines: 157-178.

---

## File Summary
- Total declarations: 10 theorems (4 closures of `HasSimplePoleAt`, 5 linearity-of-residue, plus alias).
- Key API: `HasSimplePoleAt.{add, sub, const_mul, finset_sum}` (closure properties); `residue_{add, sub, const_mul, const_smul, const_div_sub, finset_sum}` (residue linearity).
- Unused declarations within file: none. All theorems are public exported API.
- Sorries: none.
- `set_option`: none.
- Long proofs (>10 lines): `HasSimplePoleAt.finset_sum` (~18 lines, `Finset.induction` with `Classical.choose`-style destruction); `residue_finset_sum` (~22 lines, `Finset.induction` using `residue_congr` and `residue_add`).
- Purpose: Provides basic linearity of `residue` for functions with simple-pole decompositions. Closure properties (add/sub/const_mul/finset_sum) of `HasSimplePoleAt` are established by manipulating coefficients and regular parts; the residue linearity then follows by invoking `residue_eq_of_simple_pole_decomp` and `residue_eq_coeff`. Also includes the basic identity `residue (c/(z-s)) s = c`. These lemmas are the bridge layer between the project's additive simple-pole structure and standard residue calculus.
