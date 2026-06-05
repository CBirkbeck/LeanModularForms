/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GL2.HeckeT_p_Gamma0

/-!
# Ring-side Hecke elements `D_n` in `𝕋(Γ₀(N))`

This file is the **ring layer** of the ring-first Hecke-operator architecture: it defines,
purely inside the Hecke ring `𝕋 (Gamma0_pair N) ℤ` (commutative by Shimura Prop 3.8 for
`Γ₀(N)`, via the Atkin–Lehner anti-involution), the elements whose images under the
character-space ring homomorphisms *are* the classical Hecke operators:

* `heckeRingDp p`     — the prime class `Γ₀(N)·diag(1,p)·Γ₀(N)` (defined for **all** `p > 0`,
  including the bad primes `p ∣ N`);
* `heckeRingSpp p`    — the scalar class `Γ₀(N)·diag(p,p)·Γ₀(N)` for `p ∤ N`, and `0` for
  `p ∣ N` (the scalar matrix `diag(p,p)` does not lie in `Δ₀(N)` when `p ∣ N`; the junk
  value `0` mirrors the vanishing of the diamond operator `⟨p⟩` there);
* `heckeRingD_ppow p r` — the prime-power element defined by the Diamond–Shurman
  recurrence `D_{p^{r+2}} = D_p·D_{p^{r+1}} − (p·S_p)·D_{p^r}`, which for `p ∣ N`
  degenerates (since `S_p = 0`) to `D_{p^r} = D_p^r`;
* `heckeRingD_n n`    — the composite element, assembled multiplicatively over the prime
  factorisation of `n` by `minFac`-peeling, with **genuine** bad-prime factors.

The structural identities — commutativity (free), the per-prime product formula
`D_{p^r}·D_{p^s} = ∑_{i ≤ min(r,s)} (p·S_p)^i · D_{p^{r+s−2i}}`, and coprime
multiplicativity `D_m·D_n = D_{mn}` — are **pure commutative algebra**: they are proven
below for an arbitrary commutative ring (the `Formal*` sections) and then instantiated at
`𝕋 (Gamma0_pair N) ℤ`.  No operators, coset combinatorics, or analytic input appear.
The operator-level counterparts (`heckeT_n_comm`, `heckeT_n_mul_coprime`, …) are then
*transported* along `heckeRingHomCharSpace` and glued over the character direct sum,
replacing their former self-contained induction cascades.

## Main definitions

* `HeckeRing.GL2.Unified.heckeRingSpp`
* `HeckeRing.GL2.Unified.heckeRingD_ppow`
* `HeckeRing.GL2.Unified.heckeRingD_n`
* `HeckeRing.GL2.Unified.heckeRingS_n` — the composite scalar class `S_d` (multiplicative
  in `d`; vanishes unless `d` is coprime to `N`), the ring-side avatar of `d^{k-2}·⟨d⟩`.

## Main results

* `heckeRingD_ppow_mul`  — the per-prime product formula (Chebyshev-style algebra).
* `heckeRingD_n_mul_coprime` — `D_{mn} = D_m · D_n` for coprime `m, n`.
-/

namespace HeckeRing.GL2.Unified

open HeckeRing HeckeRing.GLn

/-! ## Formal commutative algebra

The recurrence and peeling constructions, over an arbitrary commutative ring.  Everything
here is instance-clean: `𝕋 (Gamma0_pair N) ℤ` carries both a global `Ring` instance and a
(non-instance) `CommRing` structure `instCommRing_Gamma0`, and stating the algebra
generically avoids ever mixing the two elaboration paths. -/

section FormalChebyshev

variable {R : Type*} [CommRing R]

/-- Formal rank-one product step: if `d` satisfies the Hecke recurrence
`d (r+2) = D·d (r+1) − S·d r`, then `D · d m = d (m+1) + S · d (m−1)` for `m ≥ 1`. -/
private theorem formal_D_mul_d (D S : R) (d : ℕ → R)
    (hrec : ∀ r, d (r + 2) = D * d (r + 1) - S * d r) (m : ℕ) (hm : 0 < m) :
    D * d m = d (m + 1) + S * d (m - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [show m + 1 + 1 = m + 2 from rfl, hrec m, Nat.add_sub_cancel]
  ring

/-- **Formal Chebyshev-style product formula**: if `d 0 = 1`, `d 1 = D` and
`d (r+2) = D·d (r+1) − S·d r`, then for `r ≤ s`
`d r · d s = ∑_{i=0}^{r} S^i · d (r+s−2i)`. -/
private theorem formal_ppow_mul (D S : R) (d : ℕ → R) (h0 : d 0 = 1) (h1 : d 1 = D)
    (hrec : ∀ r, d (r + 2) = D * d (r + 1) - S * d r) :
    ∀ r s : ℕ, r ≤ s →
      d r * d s = ∑ i ∈ Finset.range (r + 1), S ^ i * d (r + s - 2 * i) := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro s hrs
    match r, ih with
    | 0, _ => simp [h0]
    | 1, _ =>
      rw [h1, formal_D_mul_d D S d hrec s (by omega),
        Finset.sum_range_succ, Finset.sum_range_one, pow_zero, one_mul, pow_one,
        show 1 + s - 2 * 0 = s + 1 by omega, show 1 + s - 2 * 1 = s - 1 by omega]
    | (r + 2), ih =>
      have key : ∀ i ∈ Finset.range (r + 2),
          D * (S ^ i * d (r + 1 + s - 2 * i)) =
            S ^ i * d (r + 2 + s - 2 * i) + S ^ (i + 1) * d (r + s - 2 * i) := by
        intro i hi
        rw [Finset.mem_range] at hi
        have h := formal_D_mul_d D S d hrec (r + 1 + s - 2 * i) (by omega)
        rw [show r + 1 + s - 2 * i + 1 = r + 2 + s - 2 * i by omega,
          show r + 1 + s - 2 * i - 1 = r + s - 2 * i by omega] at h
        calc D * (S ^ i * d (r + 1 + s - 2 * i))
            = S ^ i * (D * d (r + 1 + s - 2 * i)) := by ring
          _ = S ^ i * (d (r + 2 + s - 2 * i) + S * d (r + s - 2 * i)) := by rw [h]
          _ = _ := by ring
      have hL : d (r + 2) * d s = D * (d (r + 1) * d s) - S * (d r * d s) := by
        rw [hrec r]; ring
      rw [hL, ih (r + 1) (by omega) s (by omega), ih r (by omega) s (by omega),
        Finset.mul_sum, Finset.sum_congr rfl key, Finset.sum_add_distrib]
      have hshift : S * ∑ i ∈ Finset.range (r + 1), S ^ i * d (r + s - 2 * i) =
          ∑ i ∈ Finset.range (r + 1), S ^ (i + 1) * d (r + s - 2 * i) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ ↦ by ring
      rw [hshift, Finset.sum_range_succ (fun i ↦ S ^ (i + 1) * d (r + s - 2 * i)) (r + 1),
        Finset.sum_range_succ (fun i ↦ S ^ i * d (r + 2 + s - 2 * i)) (r + 2),
        show r + 2 + s - 2 * (r + 2) = r + s - 2 * (r + 1) by omega]
      ring

end FormalChebyshev

section FormalPeel

variable {R : Type*} [Monoid R]

/-- The `minFac`-peeling product: `peelProd f n = f p v · peelProd f (n / p^v)` where
`p = minFac n` and `v = v_p(n)`, with `peelProd f 0 = peelProd f 1 = 1`.  The block map
`f : ℕ → ℕ → R` is only ever evaluated at `(p, v_p(n))` with `p` prime. -/
private noncomputable def peelProd (f : ℕ → ℕ → R) (n : ℕ) : R :=
  if _h : n ≤ 1 then 1
  else
    let p := n.minFac
    let v := n.factorization p
    f p v * peelProd f (n / p ^ v)
termination_by n
decreasing_by
  have hp := Nat.minFac_prime (by omega : n ≠ 1)
  exact Nat.div_lt_self (by omega) (Nat.one_lt_pow
    (hp.factorization_pos_of_dvd (by omega) (Nat.minFac_dvd n)).ne' hp.one_lt)

@[simp] private theorem peelProd_zero (f : ℕ → ℕ → R) : peelProd f 0 = 1 := by
  rw [peelProd]; simp

@[simp] private theorem peelProd_one (f : ℕ → ℕ → R) : peelProd f 1 = 1 := by
  rw [peelProd]; simp

private theorem peelProd_peel (f : ℕ → ℕ → R) (n : ℕ) (hn : 1 < n) :
    peelProd f n =
      f n.minFac (n.factorization n.minFac) *
        peelProd f (n / n.minFac ^ n.factorization n.minFac) := by
  conv_lhs => rw [peelProd]
  rw [dif_neg (by omega : ¬ n ≤ 1)]

/-- `peelProd` over a prime power is a single block. -/
private theorem peelProd_ppow (f : ℕ → ℕ → R) {p : ℕ} (hp : Nat.Prime p) (v : ℕ)
    (hv : 0 < v) : peelProd f (p ^ v) = f p v := by
  have h1 : 1 < p ^ v := Nat.one_lt_pow hv.ne' hp.one_lt
  have hminFac : (p ^ v).minFac = p := hp.pow_minFac hv.ne'
  have hfact : (p ^ v).factorization p = v := by
    rw [hp.factorization_pow, Finsupp.single_eq_same]
  rw [peelProd_peel f _ h1, hminFac, hfact, Nat.div_self (pow_pos hp.pos v),
    peelProd_one, mul_one]

end FormalPeel

section FormalPeelComm

variable {R : Type*} [CommMonoid R]

/-- **`peelProd` is multiplicative on coprime arguments** — for any block map `f`.
Pure commutative algebra: the blocks of `m·n` are the disjoint union of the blocks of
`m` and `n`, and commutativity reorders the product. -/
private theorem peelProd_mul_coprime (f : ℕ → ℕ → R) :
    ∀ m n : ℕ, Nat.Coprime m n → peelProd f (m * n) = peelProd f m * peelProd f n := by
  -- Strong induction on the product `m * n`.
  suffices H : ∀ t m n : ℕ, m * n = t → Nat.Coprime m n →
      peelProd f (m * n) = peelProd f m * peelProd f n by
    exact fun m n h ↦ H (m * n) m n rfl h
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro m n hmn hcop
    -- Degenerate cases: a factor ≤ 1 (coprimality forces the other to be 1 when one is 0).
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [Nat.coprime_zero_left] at hcop; subst hcop; simp
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [Nat.coprime_zero_right] at hcop; subst hcop; simp
    rcases eq_or_ne m 1 with rfl | hm1'
    · rw [one_mul, peelProd_one, one_mul]
    rcases eq_or_ne n 1 with rfl | hn1'
    · rw [mul_one, peelProd_one, mul_one]
    have hm1 : 1 < m := by omega
    have hn1 : 1 < n := by omega
    -- Both factors exceed 1.  Peel the smallest prime `q` of `m*n`; it divides exactly
    -- one of the factors, and the two branches are symmetric.
    have hmn1 : 1 < m * n := by
      calc 1 < m := hm1
      _ ≤ m * n := Nat.le_mul_of_pos_right m hn
    set q := (m * n).minFac with hq_def
    have hq : Nat.Prime q := Nat.minFac_prime (by omega)
    have hq_dvd : q ∣ m * n := Nat.minFac_dvd _
    rcases (Nat.Prime.dvd_mul hq).mp hq_dvd with hqm | hqn
    · -- `q ∣ m`: the `q`-block of `m*n` is the `q`-block of `m`.
      have hqn' : ¬ q ∣ n := fun hqn ↦
        hq.ne_one (Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd hqm hqn))
      have hfac : (m * n).factorization q = m.factorization q := by
        rw [Nat.factorization_mul hm.ne' hn.ne']
        simp [Nat.factorization_eq_zero_of_not_dvd hqn']
      have hvq : 0 < m.factorization q :=
        Nat.Prime.factorization_pos_of_dvd hq hm.ne' hqm
      have hq_min_m : m.minFac = q := by
        refine le_antisymm (Nat.minFac_le_of_dvd hq.two_le hqm) ?_
        rw [hq_def]
        exact Nat.minFac_le_of_dvd (Nat.minFac_prime (by omega : m ≠ 1)).two_le
          ((Nat.minFac_dvd m).trans (Dvd.intro n rfl))
      set v := m.factorization q with hv_def
      obtain ⟨m', hm'⟩ : q ^ v ∣ m := Nat.ordProj_dvd m q
      have hqv1 : 1 < q ^ v := Nat.one_lt_pow hvq.ne' hq.one_lt
      have hm'_pos : 0 < m' := by
        rcases Nat.eq_zero_or_pos m' with rfl | h
        · rw [mul_zero] at hm'; omega
        · exact h
      have hdiv_m : m / q ^ v = m' := by
        rw [hm']; exact Nat.mul_div_cancel_left m' (by positivity)
      have hdiv_mn : m * n / q ^ v = m' * n := by
        rw [hm', mul_assoc]; exact Nat.mul_div_cancel_left _ (by positivity)
      have hcop' : Nat.Coprime m' n :=
        Nat.Coprime.coprime_dvd_left ⟨q ^ v, by rw [hm']; ring⟩ hcop
      have hm'_lt : m' < m := by
        rw [hm']; exact (Nat.lt_mul_iff_one_lt_left hm'_pos).mpr hqv1
      have hlt : m' * n < t := by
        rw [← hmn]; exact Nat.mul_lt_mul_of_lt_of_le hm'_lt le_rfl hn
      rw [peelProd_peel f (m * n) hmn1, ← hq_def, hfac, hdiv_mn,
        peelProd_peel f m hm1, hq_min_m, ← hv_def, hdiv_m,
        ih (m' * n) hlt m' n rfl hcop', mul_assoc]
    · -- `q ∣ n`: symmetric, with a `mul_left_comm` to reorder the blocks.
      have hqm' : ¬ q ∣ m := fun hqm ↦
        hq.ne_one (Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd hqm hqn))
      have hfac : (m * n).factorization q = n.factorization q := by
        rw [Nat.factorization_mul hm.ne' hn.ne']
        simp [Nat.factorization_eq_zero_of_not_dvd hqm']
      have hvq : 0 < n.factorization q :=
        Nat.Prime.factorization_pos_of_dvd hq hn.ne' hqn
      have hq_min_n : n.minFac = q := by
        refine le_antisymm (Nat.minFac_le_of_dvd hq.two_le hqn) ?_
        rw [hq_def]
        exact Nat.minFac_le_of_dvd (Nat.minFac_prime (by omega : n ≠ 1)).two_le
          ((Nat.minFac_dvd n).trans (Dvd.intro_left m rfl))
      set v := n.factorization q with hv_def
      obtain ⟨n', hn'⟩ : q ^ v ∣ n := Nat.ordProj_dvd n q
      have hqv1 : 1 < q ^ v := Nat.one_lt_pow hvq.ne' hq.one_lt
      have hn'_pos : 0 < n' := by
        rcases Nat.eq_zero_or_pos n' with rfl | h
        · rw [mul_zero] at hn'; omega
        · exact h
      have hdiv_n : n / q ^ v = n' := by
        rw [hn']; exact Nat.mul_div_cancel_left n' (by positivity)
      have hdiv_mn : m * n / q ^ v = m * n' := by
        rw [hn', show m * (q ^ v * n') = q ^ v * (m * n') by ring]
        exact Nat.mul_div_cancel_left _ (by positivity)
      have hcop' : Nat.Coprime m n' :=
        Nat.Coprime.coprime_dvd_right ⟨q ^ v, by rw [hn']; ring⟩ hcop
      have hn'_lt : n' < n := by
        rw [hn']; exact (Nat.lt_mul_iff_one_lt_left hn'_pos).mpr hqv1
      have hlt : m * n' < t := by
        rw [← hmn]; exact Nat.mul_lt_mul_of_le_of_lt le_rfl hn'_lt hm
      rw [peelProd_peel f (m * n) hmn1, ← hq_def, hfac, hdiv_mn,
        peelProd_peel f n hn1, hq_min_n, ← hv_def, hdiv_n,
        ih (m * n') hlt m n' rfl hcop', mul_left_comm]

end FormalPeelComm

/-! ## Formal general multiplication table

The ring-side Shimura 3.24: for two `peelProd`-assembled families `D = peelProd dblk` and
`S = peelProd sblk` over a commutative ring, whose prime-power blocks satisfy the
Chebyshev-style per-prime product law, the general product `D_m · D_n` expands as a sum over
the divisors of `gcd m n`.  Mirrors the operator-side `heckeT_n_mul` combinatorics
(induction on the gcd, peeling its maximal prime power, reindexing the divisor sum via
`d ↔ (p^i, d')`), with every operator manipulation replaced by commutative-ring algebra. -/

section FormalTable

variable {R : Type*} [CommRing R]

/-! ### Pure-`ℕ` divisor combinatorics

These are copies of the (private) pure-`ℕ` helpers from the operator layer `HeckeT_n.lean`;
they are reproduced here because this file may not import the operator layer. -/

/-- `p`-adic valuation of `g · p^c` is `c` when `p ∤ g`. -/
private lemma factorization_coprime_mul_pow_self {p g c : ℕ} (hp : Nat.Prime p)
    (hpg : ¬p ∣ g) : (g * p ^ c).factorization p = c := by
  rw [Nat.factorization_mul_apply_of_coprime (hp.coprime_pow_of_not_dvd hpg),
    Nat.factorization_eq_zero_of_not_dvd hpg,
    Nat.Prime.factorization_pow hp, Finsupp.single_apply, if_pos rfl, zero_add]

/-- `p`-adic valuation of `p^j · d` is `j` when `p ∤ d` and `d > 0`. -/
private lemma factorization_pow_mul_self {p j d : ℕ} (hp : Nat.Prime p) (hd_pos : 0 < d)
    (hpd : ¬p ∣ d) : (p ^ j * d).factorization p = j := by
  rw [Nat.factorization_mul (pow_pos hp.pos j).ne' hd_pos.ne', Finsupp.coe_add, Pi.add_apply,
    hp.factorization_pow, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hpd, add_zero]

/-- Forward map well-definedness for the divisor-sum bijection: `p^j · d'` divides `m·n`
when `d' ∣ g'`, `j ≤ c` and `gcd m n = g' · p^c`. -/
private lemma pow_mul_mem_gcd_divisors {p m n g' c j d' : ℕ} (_hp : Nat.Prime p)
    (hgcd_eq : m.gcd n = g' * p ^ c) (hg'_pos : 0 < g') (hpc_pos : 0 < p ^ c)
    (hd' : d' ∈ g'.divisors) (hj_le : j ≤ c) :
    p ^ j * d' ∈ (m.gcd n).divisors := by
  rw [hgcd_eq, Nat.mem_divisors]
  exact ⟨mul_comm (p ^ j) d' ▸
    Nat.mul_dvd_mul (Nat.dvd_of_mem_divisors hd') (pow_dvd_pow p hj_le),
    (Nat.mul_pos hg'_pos hpc_pos).ne'⟩

/-- Backward map well-definedness: `d / p^(v_p d) ∈ g'.divisors` when `d ∣ g' · p^c`,
`p ∤ g'`. -/
private lemma ordCompl_mem_divisors_of_dvd_mul_pow {p g' c d : ℕ} (hp : Nat.Prime p)
    (hg'_pos : 0 < g') (hpc_pos : 0 < p ^ c) (hp_not_dvd_g' : ¬p ∣ g')
    (hd_dvd_gpc : d ∣ g' * p ^ c) :
    d / p ^ d.factorization p ∈ g'.divisors := by
  have hordCompl_gpc : g' * p ^ c / p ^ (g' * p ^ c).factorization p = g' := by
    rw [factorization_coprime_mul_pow_self hp hp_not_dvd_g', Nat.mul_div_cancel g' hpc_pos]
  rw [Nat.mem_divisors]
  refine ⟨?_, hg'_pos.ne'⟩
  have := Nat.ordCompl_dvd_ordCompl_of_dvd hd_dvd_gpc p
  rwa [hordCompl_gpc] at this

/-- Decomposition of `gcd m n` after extracting `p`-powers: when `m = p^va·m'`, `n = p^vb·n'`
with `p ∤ m'`, `p ∤ n'`, then `gcd m n = gcd m' n' · p^(min va vb)`. -/
private lemma gcd_eq_gcd_ordCompl_mul_pow_min {p va vb m' n' m n : ℕ}
    (hp : Nat.Prime p) (hm_eq : m = p ^ va * m') (hn_eq : n = p ^ vb * n')
    (hp_not_dvd_m' : ¬p ∣ m') (hp_not_dvd_n' : ¬p ∣ n') :
    Nat.gcd m n = Nat.gcd m' n' * p ^ min va vb := by
  have hpa_cop_m' : Nat.Coprime (p ^ va) m' := (hp.coprime_pow_of_not_dvd hp_not_dvd_m').symm
  have hpa_cop_n' : Nat.Coprime (p ^ va) n' := (hp.coprime_pow_of_not_dvd hp_not_dvd_n').symm
  have hm'_cop_pb : Nat.Coprime m' (p ^ vb) := hp.coprime_pow_of_not_dvd hp_not_dvd_m'
  have hgcd_pp : Nat.gcd (p ^ va) (p ^ vb) = p ^ min va vb := by
    rcases le_or_gt va vb with h | h
    · rw [min_eq_left h]; exact Nat.gcd_eq_left (pow_dvd_pow p h)
    · rw [min_eq_right h.le]; exact Nat.gcd_eq_right (pow_dvd_pow p h.le)
  rw [hm_eq, hn_eq, hpa_cop_m'.mul_gcd _,
      Nat.Coprime.gcd_mul_right_cancel_right _ hpa_cop_n'.symm,
      Nat.Coprime.gcd_mul_left_cancel_right _ hm'_cop_pb.symm, hgcd_pp, mul_comm]

/-- The pure-`ℕ` index identity underlying the divisor-sum summand:
`m·n / ((p^j·d')²) = p^{min+max-2j} · (m'·n'/(d'·d'))`, together with coprimality of the two
factors, when `m = p^va·m'`, `n = p^vb·n'`, `p ∤ m'`, `p ∤ n'`, `d' ∣ gcd m' n'`. -/
private lemma mn_div_pjd_eq {p va vb m' n' m n d' j : ℕ} (hp : Nat.Prime p)
    (hm_eq : m = p ^ va * m') (hn_eq : n = p ^ vb * n')
    (hp_not_dvd_m' : ¬p ∣ m') (hp_not_dvd_n' : ¬p ∣ n')
    (hd'_dvd_m' : d' ∣ m') (hd'_dvd_n' : d' ∣ n') (_hd'_pos : 0 < d')
    (_hm'_pos : 0 < m') (_hn'_pos : 0 < n') (hj_le : j ≤ min va vb) :
    m * n / (p ^ j * d' * (p ^ j * d')) =
        p ^ (min va vb + max va vb - 2 * j) * (m' * n' / (d' * d')) ∧
      Nat.Coprime (p ^ (min va vb + max va vb - 2 * j)) (m' * n' / (d' * d')) := by
  have hdd_dvd : d' * d' ∣ m' * n' := Nat.mul_dvd_mul hd'_dvd_m' hd'_dvd_n'
  set r := va + vb - 2 * j with hr_def
  have hr_eq : min va vb + max va vb - 2 * j = r := by rw [min_add_max]
  have hmn_div_eq : m * n / (p ^ j * d' * (p ^ j * d')) =
      p ^ r * (m' * n' / (d' * d')) := by
    rw [hm_eq, hn_eq]
    have h1 : p ^ va * m' * (p ^ vb * n') = p ^ (va + vb) * (m' * n') := by rw [pow_add]; ring
    have h2 : p ^ j * d' * (p ^ j * d') = p ^ (2 * j) * (d' * d') := by
      rw [show 2 * j = j + j by omega, pow_add]; ring
    rw [h1, h2, show va + vb = 2 * j + r by omega, pow_add, mul_assoc,
        Nat.mul_div_mul_left _ _ (pow_pos hp.pos (2 * j)), Nat.mul_div_assoc _ hdd_dvd]
  have hp_not_dvd_quot : ¬p ∣ (m' * n' / (d' * d')) := by
    intro h
    have h3 : p ∣ m' * n' :=
      dvd_trans (dvd_mul_left p (d' * d')) ((Nat.dvd_div_iff_mul_dvd hdd_dvd).mp h)
    exact hp_not_dvd_m' ((hp.dvd_mul.mp h3).elim id (fun h ↦ absurd h hp_not_dvd_n'))
  exact ⟨hr_eq ▸ hmn_div_eq,
    hr_eq ▸ (hp.coprime_iff_not_dvd.mpr hp_not_dvd_quot).pow_left r⟩

/-! ### The ring algebra of the table -/

variable (dblk sblk : ℕ → ℕ → R)

/-- The summand-matching identity for the divisor-sum reindexing: the product of the
`(j, d')` term of the prime-power sum and the `d'` term of the `m'·n'` divisor sum equals
the `p^j·d'` term of the `m·n` divisor sum. -/
private lemma formal_table_summand {p : ℕ} (hp : Nat.Prime p) (va vb m' n' m n j d' : ℕ)
    (hm'_pos : 0 < m') (hn'_pos : 0 < n')
    (hm_eq : m = p ^ va * m') (hn_eq : n = p ^ vb * n')
    (hp_not_dvd_m' : ¬p ∣ m') (hp_not_dvd_n' : ¬p ∣ n')
    (hd' : d' ∈ (m'.gcd n').divisors) (hj_le : j ≤ min va vb) :
    ((p : ℤ) ^ j • (peelProd sblk (p ^ j) *
        peelProd dblk (p ^ (min va vb + max va vb - 2 * j)))) *
      ((d' : ℤ) • (peelProd sblk d' * peelProd dblk (m' * n' / (d' * d')))) =
    ((p ^ j * d' : ℕ) : ℤ) •
      (peelProd sblk (p ^ j * d') * peelProd dblk (m * n / (p ^ j * d' * (p ^ j * d')))) := by
  have hd'_dvd_g' : d' ∣ m'.gcd n' := Nat.dvd_of_mem_divisors hd'
  have hd'_dvd_m' : d' ∣ m' := dvd_trans hd'_dvd_g' (Nat.gcd_dvd_left m' n')
  have hd'_dvd_n' : d' ∣ n' := dvd_trans hd'_dvd_g' (Nat.gcd_dvd_right m' n')
  have hd'_pos : 0 < d' :=
    Nat.pos_of_ne_zero fun h ↦ (Nat.mem_divisors.mp hd').2
      (Nat.eq_zero_of_zero_dvd (h ▸ hd'_dvd_g'))
  -- `p ∤ d'`, so `p^j` and `d'` are coprime.
  have hp_not_dvd_d' : ¬p ∣ d' := fun h ↦ hp_not_dvd_m' (dvd_trans h hd'_dvd_m')
  have hcop_S : Nat.Coprime (p ^ j) d' := (hp.coprime_iff_not_dvd.mpr hp_not_dvd_d').pow_left j
  -- The `ℕ`-index identity and coprimality of the two `D`-factors.
  obtain ⟨hidx, hcop_D⟩ := mn_div_pjd_eq hp hm_eq hn_eq hp_not_dvd_m' hp_not_dvd_n'
    hd'_dvd_m' hd'_dvd_n' hd'_pos hm'_pos hn'_pos hj_le
  rw [smul_mul_smul_comm, hidx, peelProd_mul_coprime dblk _ _ hcop_D,
      peelProd_mul_coprime sblk _ _ hcop_S, Nat.cast_mul, Nat.cast_pow]
  congr 1
  ring

/-- The divisor-sum reindexing: the product of the prime-power sum and the `m'·n'` divisor
sum equals the `m·n` divisor sum, via the bijection `(j, d') ↔ p^j·d'`. -/
private lemma formal_table_div_sum {p : ℕ} (hp : Nat.Prime p) (va vb m' n' m n : ℕ)
    (hm'_pos : 0 < m') (hn'_pos : 0 < n')
    (hm_eq : m = p ^ va * m') (hn_eq : n = p ^ vb * n')
    (hp_not_dvd_m' : ¬p ∣ m') (hp_not_dvd_n' : ¬p ∣ n')
    (hgcd_eq : Nat.gcd m n = Nat.gcd m' n' * p ^ min va vb) :
    (∑ j ∈ Finset.range (min va vb + 1),
        (p : ℤ) ^ j • (peelProd sblk (p ^ j) *
          peelProd dblk (p ^ (min va vb + max va vb - 2 * j)))) *
      (∑ d ∈ (Nat.gcd m' n').divisors.attach,
        (d.val : ℤ) • (peelProd sblk d.val *
          peelProd dblk (m' * n' / (d.val * d.val)))) =
    ∑ d ∈ (Nat.gcd m n).divisors.attach,
      (d.val : ℤ) • (peelProd sblk d.val *
        peelProd dblk (m * n / (d.val * d.val))) := by
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  set c := min va vb with hc_def
  set g' := m'.gcd n' with hg'_def
  have hg'_pos : 0 < g' :=
    Nat.pos_of_ne_zero fun h ↦ absurd (Nat.eq_zero_of_gcd_eq_zero_left h) hm'_pos.ne'
  have hpc_pos : 0 < p ^ c := pow_pos hp.pos c
  have hp_not_dvd_g' : ¬p ∣ g' := fun h ↦
    hp_not_dvd_m' (dvd_trans (dvd_trans h (Nat.gcd_dvd_left m' n')) (dvd_refl m'))
  refine Finset.sum_bij'
    (fun (x : ℕ × {d // d ∈ g'.divisors})
        (hx : x ∈ Finset.range (c + 1) ×ˢ g'.divisors.attach) ↦
      ⟨p ^ x.1 * x.2.val, ?_⟩)
    (fun (d : {d // d ∈ (m.gcd n).divisors}) (_ : d ∈ (m.gcd n).divisors.attach) ↦
      ((d.val.factorization p), ⟨d.val / p ^ (d.val.factorization p), ?_⟩))
    ?_ ?_ ?_ ?_ ?_
  case refine_1 =>
    exact pow_mul_mem_gcd_divisors hp hgcd_eq hg'_pos hpc_pos x.2.prop
      (Nat.lt_add_one_iff.mp (Finset.mem_range.mp (Finset.mem_product.mp hx).1))
  case refine_2 =>
    exact ordCompl_mem_divisors_of_dvd_mul_pow hp hg'_pos hpc_pos hp_not_dvd_g'
      (hgcd_eq ▸ Nat.dvd_of_mem_divisors d.prop)
  case refine_3 => exact fun _ _ ↦ Finset.mem_attach _ _
  case refine_4 =>
    intro ⟨d, hd⟩ _
    simp only [Finset.mem_product, Finset.mem_range, Finset.mem_attach, and_true]
    have hd_dvd_gpc : d ∣ g' * p ^ c := hgcd_eq ▸ Nat.dvd_of_mem_divisors hd
    have hgpc_ne : g' * p ^ c ≠ 0 := (Nat.mul_pos hg'_pos hpc_pos).ne'
    have hd_ne : d ≠ 0 := fun h ↦ hgpc_ne (by rw [← Nat.zero_dvd]; exact h ▸ hd_dvd_gpc)
    exact Nat.lt_succ_of_le (factorization_coprime_mul_pow_self (c := c) hp hp_not_dvd_g' ▸
      (Nat.factorization_le_iff_dvd hd_ne hgpc_ne).mpr hd_dvd_gpc p)
  case refine_5 =>
    rintro ⟨j, ⟨d', hd'⟩⟩ -
    have hd'_pos : 0 < d' := Nat.pos_of_ne_zero fun h ↦
      hg'_pos.ne' (Nat.eq_zero_of_zero_dvd (h ▸ Nat.dvd_of_mem_divisors hd'))
    have hfact : (p ^ j * d').factorization p = j :=
      factorization_pow_mul_self hp hd'_pos
        (fun h ↦ hp_not_dvd_g' (dvd_trans h (Nat.dvd_of_mem_divisors hd')))
    ext1
    · exact hfact
    · exact Subtype.ext (by simp only [hfact, Nat.mul_div_cancel_left d' (pow_pos hp.pos j)])
  case refine_6 =>
    rintro ⟨d, hd⟩ -
    exact Subtype.ext (Nat.ordProj_mul_ordCompl_eq_self d p)
  case refine_7 =>
    rintro ⟨j, ⟨d', hd'⟩⟩ hmem
    exact formal_table_summand dblk sblk hp va vb m' n' m n j d' hm'_pos hn'_pos
      hm_eq hn_eq hp_not_dvd_m' hp_not_dvd_n' hd'
      (Nat.lt_add_one_iff.mp (Finset.mem_range.mp (Finset.mem_product.mp hmem).1))

/-- The non-coprime inductive step of `formal_table`: peel the maximal prime power of
`gcd m n`, reduce the two same-prime power factors via the per-prime law `hppow`, apply the
inductive hypothesis on the strictly smaller gcd `gcd m' n'`, and reindex. -/
private theorem formal_table_noncoprime
    (hppow : ∀ (p : ℕ), Nat.Prime p → ∀ r s : ℕ, r ≤ s →
      peelProd dblk (p ^ r) * peelProd dblk (p ^ s) =
        ∑ i ∈ Finset.range (r + 1),
          (p : ℤ) ^ i • (peelProd sblk (p ^ i) * peelProd dblk (p ^ (r + s - 2 * i))))
    (g : ℕ) (m n : ℕ) [NeZero m] [NeZero n] (hg : Nat.gcd m n = g) (hg1 : g ≠ 1)
    (ih : ∀ g', g' < g → ∀ (m' n' : ℕ), [NeZero m'] → [NeZero n'] → Nat.gcd m' n' = g' →
      peelProd dblk m' * peelProd dblk n' =
        ∑ d ∈ (Nat.gcd m' n').divisors.attach,
          (d.val : ℤ) • (peelProd sblk d.val *
            peelProd dblk (m' * n' / (d.val * d.val)))) :
    peelProd dblk m * peelProd dblk n =
      ∑ d ∈ (Nat.gcd m n).divisors.attach,
        (d.val : ℤ) • (peelProd sblk d.val *
          peelProd dblk (m * n / (d.val * d.val))) := by
  have hg_pos : 0 < g := by
    rcases Nat.eq_zero_or_pos g with rfl | h
    · exact absurd ((Nat.gcd_eq_zero_iff.mp hg)).1 (NeZero.ne m)
    · exact h
  set p := g.minFac with hp_def
  have hp : Nat.Prime p := Nat.minFac_prime (by omega)
  have hp_dvd_m : p ∣ m := dvd_trans (hg ▸ Nat.minFac_dvd g) (Nat.gcd_dvd_left m n)
  have hp_dvd_n : p ∣ n := dvd_trans (hg ▸ Nat.minFac_dvd g) (Nat.gcd_dvd_right m n)
  set va := m.factorization p with hva_def
  set vb := n.factorization p with hvb_def
  have ha_pos : 0 < va := hp.factorization_pos_of_dvd (NeZero.ne m) hp_dvd_m
  have hb_pos : 0 < vb := hp.factorization_pos_of_dvd (NeZero.ne n) hp_dvd_n
  set m' := m / p ^ va with hm'_def
  set n' := n / p ^ vb with hn'_def
  have hm'_pos : 0 < m' :=
    Nat.div_pos (Nat.le_of_dvd (NeZero.pos m) (Nat.ordProj_dvd m p)) (pow_pos hp.pos va)
  have hn'_pos : 0 < n' :=
    Nat.div_pos (Nat.le_of_dvd (NeZero.pos n) (Nat.ordProj_dvd n p)) (pow_pos hp.pos vb)
  haveI : NeZero m' := ⟨hm'_pos.ne'⟩
  haveI : NeZero n' := ⟨hn'_pos.ne'⟩
  have hp_not_dvd_m' : ¬p ∣ m' := Nat.not_dvd_ordCompl hp (NeZero.ne m)
  have hp_not_dvd_n' : ¬p ∣ n' := Nat.not_dvd_ordCompl hp (NeZero.ne n)
  have hm_eq : m = p ^ va * m' := (Nat.mul_div_cancel' (Nat.ordProj_dvd m p)).symm
  have hn_eq : n = p ^ vb * n' := (Nat.mul_div_cancel' (Nat.ordProj_dvd n p)).symm
  have hgcd_eq : Nat.gcd m n = Nat.gcd m' n' * p ^ min va vb :=
    gcd_eq_gcd_ordCompl_mul_pow_min hp hm_eq hn_eq hp_not_dvd_m' hp_not_dvd_n'
  set g' := Nat.gcd m' n' with hg'_def
  have hg'_lt : g' < g := by
    rw [← hg, hgcd_eq]
    refine lt_mul_of_one_lt_right (Nat.pos_of_ne_zero fun hg'0 ↦ ?_)
      (Nat.one_lt_pow (by omega) hp.one_lt)
    exact hm'_pos.ne' (Nat.eq_zero_of_gcd_eq_zero_left hg'0)
  -- Coprime peeling of `D` at the maximal prime power.
  have hcop_m : Nat.Coprime (p ^ va) m' := (hp.coprime_pow_of_not_dvd hp_not_dvd_m').symm
  have hcop_n : Nat.Coprime (p ^ vb) n' := (hp.coprime_pow_of_not_dvd hp_not_dvd_n').symm
  have hDm : peelProd dblk m = peelProd dblk (p ^ va) * peelProd dblk m' := by
    rw [hm_eq, peelProd_mul_coprime dblk _ _ hcop_m]
  have hDn : peelProd dblk n = peelProd dblk (p ^ vb) * peelProd dblk n' := by
    rw [hn_eq, peelProd_mul_coprime dblk _ _ hcop_n]
  -- Reorder same-prime powers to `(min, max)`.
  have hppow_minmax : peelProd dblk (p ^ va) * peelProd dblk (p ^ vb) =
      peelProd dblk (p ^ min va vb) * peelProd dblk (p ^ max va vb) := by
    rcases le_or_gt va vb with h | h
    · rw [min_eq_left h, max_eq_right h]
    · rw [min_eq_right h.le, max_eq_left h.le, mul_comm]
  rw [hDm, hDn, show peelProd dblk (p ^ va) * peelProd dblk m' *
        (peelProd dblk (p ^ vb) * peelProd dblk n') =
      peelProd dblk (p ^ va) * peelProd dblk (p ^ vb) *
        (peelProd dblk m' * peelProd dblk n') by ring,
      hppow_minmax,
      hppow p hp (min va vb) (max va vb) (min_le_max),
      ih g' (hg ▸ hg'_lt) m' n' rfl]
  exact formal_table_div_sum dblk sblk hp va vb m' n' m n hm'_pos hn'_pos
    hm_eq hn_eq hp_not_dvd_m' hp_not_dvd_n' hgcd_eq

/-- **Formal general multiplication table** (ring-side Shimura 3.24).  For two
`peelProd`-assembled families `D = peelProd dblk` and `S = peelProd sblk` over a commutative
ring whose prime-power blocks satisfy the per-prime Chebyshev product law `hppow`,
`D_m · D_n = ∑_{d ∣ gcd m n} d • (S_d · D_{mn/d²})`. -/
private theorem formal_table
    (hppow : ∀ (p : ℕ), Nat.Prime p → ∀ r s : ℕ, r ≤ s →
      peelProd dblk (p ^ r) * peelProd dblk (p ^ s) =
        ∑ i ∈ Finset.range (r + 1),
          (p : ℤ) ^ i • (peelProd sblk (p ^ i) * peelProd dblk (p ^ (r + s - 2 * i))))
    (m n : ℕ) [NeZero m] [NeZero n] :
    peelProd dblk m * peelProd dblk n =
      ∑ d ∈ (Nat.gcd m n).divisors.attach,
        (d.val : ℤ) • (peelProd sblk d.val *
          peelProd dblk (m * n / (d.val * d.val))) := by
  suffices H : ∀ g, ∀ (m n : ℕ), [NeZero m] → [NeZero n] → Nat.gcd m n = g →
      peelProd dblk m * peelProd dblk n =
        ∑ d ∈ (Nat.gcd m n).divisors.attach,
          (d.val : ℤ) • (peelProd sblk d.val *
            peelProd dblk (m * n / (d.val * d.val))) by
    exact H (Nat.gcd m n) m n rfl
  intro g
  induction g using Nat.strong_induction_on with
  | _ g ih =>
  intro m n _ _ hg
  by_cases hg1 : g = 1
  · subst hg1
    have hmn_cop : Nat.Coprime m n := hg
    have hattach : (Nat.gcd m n).divisors.attach = {⟨1, by rw [hg]; simp⟩} := by
      have hd : (Nat.gcd m n).divisors = {1} := hg ▸ Nat.divisors_one
      ext ⟨a, ha⟩
      rw [hd] at ha
      simp only [Finset.mem_singleton] at ha ⊢
      exact ⟨fun _ ↦ Subtype.ext ha, fun _ ↦ Finset.mem_attach _ _⟩
    rw [hattach, Finset.sum_singleton]
    simp only [Nat.cast_one, one_smul, Nat.one_mul, Nat.div_one]
    rw [peelProd_one, one_mul, ← peelProd_mul_coprime dblk m n hmn_cop]
  · exact formal_table_noncoprime dblk sblk hppow g m n hg hg1
      (fun g' hlt m' n' _ _ h ↦ ih g' hlt m' n' h)

end FormalTable

variable {N : ℕ} [NeZero N]

/-! ## The ring elements -/

/-- The ring-side prime generator: the single double coset `D_p = Γ₀(N)·diag(1,p)·Γ₀(N)`.
Defined for every `p > 0`, including bad primes `p ∣ N`. -/
noncomputable def heckeRingDp (p : ℕ) (hp : 0 < p) : 𝕋 (Gamma0_pair N) ℤ :=
  T_single (Gamma0_pair N) ℤ (D_p_Gamma0 N p hp) 1

/-- The ring-side scalar generator: the single scalar double coset `T(p,p)` for `p ∤ N`,
and `0` for `p ∣ N` (where `diag(p,p) ∉ Δ₀(N)`; the vanishing mirrors `⟨p⟩ = 0`). -/
noncomputable def heckeRingSpp (p : ℕ) (hp : Nat.Prime p) : 𝕋 (Gamma0_pair N) ℤ :=
  if hpN : Nat.Coprime p N then
    T_single (Gamma0_pair N) ℤ (T_diag_Gamma0 N (fun _ : Fin 2 ↦ p) (fun _ ↦ hp.pos)
      (by rw [Int.gcd_natCast_natCast]; exact hpN)) 1
  else 0

@[simp] theorem heckeRingSpp_of_not_coprime (p : ℕ) (hp : Nat.Prime p)
    (hpN : ¬ Nat.Coprime p N) : heckeRingSpp (N := N) p hp = 0 :=
  dif_neg hpN

/-- The ring-side prime-power element, defined by the Diamond–Shurman recurrence
`D_{p^0} = 1`, `D_{p^1} = D_p`, and
`D_{p^{r+2}} = D_p · D_{p^{r+1}} − (p·S_p) · D_{p^r}`.
For `p ∣ N` the scalar term vanishes and the recurrence degenerates to `D_{p^r} = D_p^r`. -/
noncomputable def heckeRingD_ppow (p : ℕ) (hp : Nat.Prime p) :
    ℕ → 𝕋 (Gamma0_pair N) ℤ
  | 0 => 1
  | 1 => heckeRingDp p hp.pos
  | r + 2 =>
    heckeRingDp p hp.pos * heckeRingD_ppow p hp (r + 1) -
      ((p : ℤ) • heckeRingSpp p hp) * heckeRingD_ppow p hp r

@[simp] theorem heckeRingD_ppow_zero (p : ℕ) (hp : Nat.Prime p) :
    heckeRingD_ppow (N := N) p hp 0 = 1 := rfl

@[simp] theorem heckeRingD_ppow_one (p : ℕ) (hp : Nat.Prime p) :
    heckeRingD_ppow (N := N) p hp 1 = heckeRingDp p hp.pos := rfl

theorem heckeRingD_ppow_succ_succ (p : ℕ) (hp : Nat.Prime p) (r : ℕ) :
    heckeRingD_ppow (N := N) p hp (r + 2) =
      heckeRingDp p hp.pos * heckeRingD_ppow p hp (r + 1) -
        ((p : ℤ) • heckeRingSpp p hp) * heckeRingD_ppow p hp r := rfl

/-- For a bad prime `p ∣ N` the recurrence degenerates: `D_{p^r} = D_p^r`. -/
theorem heckeRingD_ppow_eq_pow_of_not_coprime (p : ℕ) (hp : Nat.Prime p)
    (hpN : ¬ Nat.Coprime p N) (r : ℕ) :
    heckeRingD_ppow (N := N) p hp r = heckeRingDp p hp.pos ^ r := by
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    match r, ih with
    | 0, _ => simp
    | 1, _ => simp
    | (r + 2), ih =>
      rw [heckeRingD_ppow_succ_succ, heckeRingSpp_of_not_coprime p hp hpN,
        smul_zero, zero_mul, sub_zero, ih (r + 1) (by omega)]
      exact (pow_succ' _ _).symm

/-- **Per-prime product formula** (Shimura 3.24(3) at level `Γ₀(N)`, ring side): for
`r ≤ s`,
`D_{p^r} · D_{p^s} = ∑_{i=0}^{r} (p·S_p)^i · D_{p^{r+s−2i}}`.
Instantiates the formal Chebyshev identity in the commutative ring `𝕋 (Gamma0_pair N) ℤ`.
For `p ∣ N` both sides collapse to `D_p^{r+s}`. -/
theorem heckeRingD_ppow_mul (p : ℕ) (hp : Nat.Prime p) (r s : ℕ) (hrs : r ≤ s) :
    heckeRingD_ppow (N := N) p hp r * heckeRingD_ppow p hp s =
      ∑ i ∈ Finset.range (r + 1),
        ((p : ℤ) • heckeRingSpp p hp) ^ i * heckeRingD_ppow p hp (r + s - 2 * i) := by
  letI : CommRing (𝕋 (Gamma0_pair N) ℤ) := instCommRing_Gamma0 N
  exact formal_ppow_mul (heckeRingDp p hp.pos) ((p : ℤ) • heckeRingSpp p hp)
    (heckeRingD_ppow p hp) rfl rfl (fun r ↦ heckeRingD_ppow_succ_succ p hp r) r s hrs

/-- The composite ring element `D_n`, assembled by `minFac`-peeling over the prime
factorisation of `n` — with **genuine** factors at bad primes `p ∣ N`
(`D_{p^v} = D_p^v`). `D_0 = D_1 = 1`. -/
noncomputable def heckeRingD_n (n : ℕ) : 𝕋 (Gamma0_pair N) ℤ :=
  peelProd (R := 𝕋 (Gamma0_pair N) ℤ)
    (fun p v ↦ if hp : Nat.Prime p then heckeRingD_ppow p hp v else 1) n

@[simp] theorem heckeRingD_n_zero : heckeRingD_n (N := N) 0 = 1 := peelProd_zero _

@[simp] theorem heckeRingD_n_one : heckeRingD_n (N := N) 1 = 1 := peelProd_one _

/-- On a prime power, the composite assembly agrees with the prime-power element. -/
theorem heckeRingD_n_ppow (p : ℕ) (hp : Nat.Prime p) (v : ℕ) :
    heckeRingD_n (N := N) (p ^ v) = heckeRingD_ppow p hp v := by
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · simp
  rw [heckeRingD_n, peelProd_ppow _ hp v hv, dif_pos hp]

theorem heckeRingD_n_peel (n : ℕ) (hn : 1 < n) :
    heckeRingD_n (N := N) n =
      heckeRingD_ppow n.minFac (Nat.minFac_prime (by omega : n ≠ 1))
          (n.factorization n.minFac) *
        heckeRingD_n (n / n.minFac ^ n.factorization n.minFac) := by
  rw [heckeRingD_n, peelProd_peel _ n hn, dif_pos (Nat.minFac_prime (by omega : n ≠ 1))]
  rfl

/-- **Coprime multiplicativity** (ring side): `D_{mn} = D_m · D_n` for coprime `m, n`. -/
theorem heckeRingD_n_mul_coprime (m n : ℕ) (hmn : Nat.Coprime m n) :
    heckeRingD_n (N := N) (m * n) = heckeRingD_n m * heckeRingD_n n := by
  letI : CommRing (𝕋 (Gamma0_pair N) ℤ) := instCommRing_Gamma0 N
  exact peelProd_mul_coprime _ m n hmn

/-- The composite scalar class `S_d`: multiplicative over the factorisation of `d`,
with `S_{p^v} = S_p^v`.  Vanishes (some factor is `0`) unless `d` is coprime to `N`.
Ring-side avatar of the operator `d ↦ d^{k-2}·⟨d⟩`. -/
noncomputable def heckeRingS_n (d : ℕ) : 𝕋 (Gamma0_pair N) ℤ :=
  peelProd (R := 𝕋 (Gamma0_pair N) ℤ)
    (fun p v ↦ if hp : Nat.Prime p then heckeRingSpp p hp ^ v else 1) d

@[simp] theorem heckeRingS_n_one : heckeRingS_n (N := N) 1 = 1 := peelProd_one _

/-- On a prime power, the composite scalar class agrees with the power of the prime scalar:
`S_{p^v} = S_p^v`. -/
theorem heckeRingS_n_ppow (p : ℕ) (hp : Nat.Prime p) (v : ℕ) :
    heckeRingS_n (N := N) (p ^ v) = heckeRingSpp p hp ^ v := by
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · simp
  rw [heckeRingS_n, peelProd_ppow _ hp v hv, dif_pos hp]

/-- **Per-prime product formula in composite form** (Shimura 3.24(3), ring side): for
`r ≤ s`,
`D_{p^r} · D_{p^s} = ∑_{i=0}^{r} p^i • (S_{p^i} · D_{p^{r+s−2i}})`.
This is the per-prime hypothesis required to feed the formal general table. -/
theorem heckeRingD_n_ppow_mul (p : ℕ) (hp : Nat.Prime p) (r s : ℕ) (hrs : r ≤ s) :
    heckeRingD_n (N := N) (p ^ r) * heckeRingD_n (p ^ s) =
      ∑ i ∈ Finset.range (r + 1),
        (p : ℤ) ^ i • (heckeRingS_n (p ^ i) * heckeRingD_n (p ^ (r + s - 2 * i))) := by
  rw [heckeRingD_n_ppow p hp r, heckeRingD_n_ppow p hp s, heckeRingD_ppow_mul p hp r s hrs]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [heckeRingD_n_ppow p hp, heckeRingS_n_ppow p hp, smul_pow, smul_mul_assoc]

/-- **General multiplication table** (ring-side Shimura 3.24 at level `Γ₀(N)`): for
`m, n > 0`,
`D_m · D_n = ∑_{d ∣ gcd m n} d • (S_d · D_{mn/d²})`.
The bad-prime divisors `d` with `gcd(d, N) > 1` contribute `0` (since `S_d = 0` there), so the
sum over *all* divisors of `gcd m n` is correct as stated.  Instantiates the formal table
`formal_table` with the concrete `peelProd`-assembled families `heckeRingD_n`, `heckeRingS_n`,
whose per-prime blocks satisfy the Chebyshev product law `heckeRingD_n_ppow_mul`. -/
theorem heckeRingD_n_mul (m n : ℕ) [NeZero m] [NeZero n] :
    heckeRingD_n (N := N) m * heckeRingD_n n =
      ∑ d ∈ (Nat.gcd m n).divisors.attach,
        (d.val : ℤ) • (heckeRingS_n d.val * heckeRingD_n (m * n / (d.val * d.val))) := by
  letI : CommRing (𝕋 (Gamma0_pair N) ℤ) := instCommRing_Gamma0 N
  exact formal_table
    (fun p v ↦ if hp : Nat.Prime p then heckeRingD_ppow p hp v else 1)
    (fun p v ↦ if hp : Nat.Prime p then heckeRingSpp p hp ^ v else 1)
    (fun p hp r s hrs ↦ heckeRingD_n_ppow_mul p hp r s hrs) m n

end HeckeRing.GL2.Unified
