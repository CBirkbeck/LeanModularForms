import Verso
import VersoManual
import VersoBlueprint
import LeanModularForms.HeckeRIngs.GLn.CongruenceHecke.Foundation
import LeanModularForms.HeckeRIngs.GLn.CongruenceHecke.Props
import LeanModularForms.HeckeRIngs.GLn.CongruenceHecke.AtkinLehner
import LeanModularForms.HeckeRIngs.GLn.CongruenceHecke.Surjectivity

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Congruence Hecke rings (Shimura §3.3)" =>

This chapter specialises the abstract Hecke-pair machinery to the congruence pair
$`(\Gamma_0(N), \Delta_0(N))` inside $`\mathrm{GL}_2(\mathbb{Q})`. After fixing the pair itself,
we record Shimura's Propositions 3.31–3.33 on the double cosets of coprime determinant and the
remaining *bad* classes, and the commutativity of the congruence Hecke ring obtained from an
Atkin–Lehner-style anti-involution. The chapter culminates in Shimura's Theorem 3.35: the
surjection $`R(\Gamma,\Delta)\to R(\Gamma_0(N),\Delta_0(N))` comparing the full $`\mathrm{GL}_2`
Hecke ring with its level-$`N` quotient \[Sh, §3.3\].

:::definition "gamma0-pair" (lean := "HeckeRing.GLn.Gamma0_pair")
*The congruence Hecke pair $`(\Gamma_0(N), \Delta_0(N))`.*
Fix a positive integer $`N`. The group $`\Gamma_0(N)` is the congruence subgroup of
$`SL_2(\mathbb{Z})` consisting of those matrices whose lower-left entry is $`\equiv 0 \pmod N`,
regarded inside $`\mathrm{GL}_2(\mathbb{Q})`. The submonoid $`\Delta_0(N)\le\mathrm{GL}_2(\mathbb{Q})`
consists of those $`g` that are integral (admit an integer-matrix representative $`A`) with
positive determinant and such that the lower-left entry satisfies $`N\mid A_{1,0}` while the
top-left entry is coprime to $`N`, $`\gcd(A_{0,0}, N)=1`; this is Shimura's set (3.3.1). One has
$`\Gamma_0(N)\le\Delta_0(N)`, since an element of $`\Gamma_0(N)` is integral of determinant $`1`
with $`N\mid A_{1,0}` and unimodular top-left entry, and $`\Delta_0(N)` lies in the commensurator
of $`\Gamma_0(N)`, because every member has positive-determinant integer entries and hence
conjugates a principal congruence subgroup into $`SL_2(\mathbb{Z})` \[Sh, §3.3, Lemma 3.10\].
These two inclusions make $`(\Gamma_0(N), \Delta_0(N))` a Hecke pair: each double coset
$`\Gamma_0(N)\backslash\Delta_0(N)/\Gamma_0(N)` decomposes into finitely many left cosets.

Depends on: {uses "hecke-pair"}[]
:::

:::theorem "shimura-prop-3-31" (lean := "HeckeRing.GLn.shimura_prop_3_31")
*Injectivity of the coset comparison on coprime-determinant classes.*
Passing from level $`N` to full level sends the double coset $`\Gamma_0(N)\,\alpha\,\Gamma_0(N)`
to $`\Gamma\,\alpha\,\Gamma`, where $`\Gamma = SL_2(\mathbb{Z})`. Let $`a, b\in\Delta_0(N)` be two
elements whose determinant is coprime to $`N` (that is, every integer-matrix representative $`A`
satisfies $`\gcd(\det A, N)=1`). If the full-level double cosets agree, $`\Gamma\,a\,\Gamma =
\Gamma\,b\,\Gamma`, then the level-$`N` double cosets already agree, $`\Gamma_0(N)\,a\,\Gamma_0(N)
= \Gamma_0(N)\,b\,\Gamma_0(N)`. Thus on classes of coprime determinant the level-$`N` double
coset is determined by its image at full level, so the comparison map is injective there
\[Sh, Prop 3.31\].

Depends on: {uses "gamma0-pair"}[]
:::

:::proof "shimura-prop-3-31"
The argument rests on Shimura's Lemma 3.29(3): for any $`\alpha\in\Delta_0(N)` whose determinant
is coprime to $`N`, intersecting the full double coset back down to the monoid recovers the
level-$`N` double coset, $`\Gamma\,\alpha\,\Gamma \cap \Delta_0(N) = \Gamma_0(N)\,\alpha\,
\Gamma_0(N)`. One inclusion is the elementary divisor relation $`\Gamma_0(N)\le\Gamma`; the
reverse direction uses the coprimality of the determinant to elementary-divisor-reduce any
full-level conjugate lying in $`\Delta_0(N)` to a $`\Gamma_0(N)`-conjugate. In particular the
level-$`N` double coset is a function of the full-level double coset alone.

Now suppose $`\Gamma\,a\,\Gamma = \Gamma\,b\,\Gamma`. Intersect both sides with the monoid
$`\Delta_0(N)`; the intersections are equal. By the lemma applied separately to $`a` and to
$`b`—both of which have coprime determinant—the left intersection equals $`\Gamma_0(N)\,a\,
\Gamma_0(N)` and the right equals $`\Gamma_0(N)\,b\,\Gamma_0(N)`. Hence these two level-$`N`
double cosets coincide, which is exactly the asserted injectivity.
:::

:::theorem "T-bad-mul" (lean := "HeckeRing.GLn.T_bad_mul")
*Multiplicativity of the bad classes.*
For the diagonal matrix $`\mathrm{diag}(1, m)`, write $`T'(m)` for the basis element of the
congruence Hecke ring attached to the double coset $`\Gamma_0(N)\,\mathrm{diag}(1,m)\,
\Gamma_0(N)`; this class is well defined whenever $`\gcd(1, N)=1`, which holds automatically.
Let $`m, n` be positive integers each dividing a power of $`N`, so that $`m \mid N^{k_m}` and
$`n \mid N^{k_n}` for some exponents $`k_m, k_n`. Then the two bad classes multiply by simply
multiplying their indices:
$$`
  T'(m)\cdot T'(n) \;=\; T'(mn).
`
In particular the subring spanned by the bad classes $`\{T'(m): m\mid N^{\infty}\}` is the
free commutative monoid algebra on these generators, and indexing is multiplicative on the
divisors of powers of $`N` \[Sh, Prop 3.33\].

Depends on: {uses "gamma0-pair"}[] {uses "T-single"}[] {uses "hecke-multiplicity"}[] {uses "deg"}[]
:::

:::proof "T-bad-mul"
The product $`T'(m)\cdot T'(n)` expands through the structure constants as
$`\sum_d \mu\bigl(\mathrm{diag}(1,m),\mathrm{diag}(1,n);d\bigr)\,T'_d`, the sum over double
cosets $`d`. Every left-coset representative of $`\Gamma_0(N)\,\mathrm{diag}(1,m)\,\Gamma_0(N)`
times one of $`\Gamma_0(N)\,\mathrm{diag}(1,n)\,\Gamma_0(N)` is an integral matrix of positive
determinant $`mn`, with lower-left entry divisible by $`N` and top-left entry coprime to $`N`,
hence a member of the monoid $`\Delta_0(N)`. Since $`mn` divides $`N^{k_m+k_n}`, the double-coset
form of Shimura's proposition forces every such product to lie in the single double coset of
$`\mathrm{diag}(1, mn)`. Thus the structure constants vanish off this one class, and the product
collapses to a single term $`\mu\cdot T'(mn)` for some multiplicity $`\mu`.

It remains to see $`\mu = 1`. The degree homomorphism is multiplicative, and the bad class of
index $`k` has degree exactly $`k`, since its left cosets are counted by the divisors of the
relevant power of $`N`. Applying the degree to both sides gives $`m\cdot n` on the left and
$`\mu\cdot(mn)` on the right; cancelling the nonzero factor $`mn` yields $`\mu = 1`, so
$`T'(m)\cdot T'(n)=T'(mn)`.
:::

:::theorem "commring-Gamma0" (lean := "HeckeRing.GLn.Gamma0_pair_HeckeAlgebra_mul_comm, HeckeRing.GLn.instCommRing_Gamma0")
*Commutativity of the congruence Hecke ring.*
The Hecke ring $`R(\Gamma_0(N),\Delta_0(N))` of the congruence pair is commutative: the basis
indexed by double cosets $`\Gamma_0(N)\backslash\Delta_0(N)/\Gamma_0(N)` carries a multiplication
satisfying $`T_1\cdot T_2 = T_2\cdot T_1` for all $`T_1, T_2`, and the ring structure upgrades
accordingly to a commutative ring \[Sh, Prop 3.8 / §3.3\].

Depends on: {uses "gamma0-pair"}[] {uses "mul-comm-of-ai"}[] {uses "shimura-prop-3-31"}[]
:::

:::proof "commring-Gamma0"
The commutativity is produced by an Atkin–Lehner-style anti-involution of the congruence pair. Set
$`w=\mathrm{diag}(1,N)`; the assignment
$$`
  g\;\longmapsto\;w\,{}^{t}g\,w^{-1}
`
reverses products and is involutive, and it preserves both the group $`\Gamma_0(N)` and the monoid
$`\Delta_0(N)`, since conjugating the transpose by $`w` keeps the lower-left entry divisible by
$`N` and the top-left entry coprime to $`N` while leaving the determinant unchanged. It is thus an
anti-involution of $`(\Gamma_0(N),\Delta_0(N))`.

By the general criterion {bpref "mul-comm-of-ai"}[], it suffices to check that this anti-involution
fixes every double coset, $`\Gamma_0(N)\,\bar g\,\Gamma_0(N)=\Gamma_0(N)\,g\,\Gamma_0(N)`. Splitting
off the content of a representative reduces the claim to primitive classes, and a two-sided
$`\Gamma_0(N)`-clearing then brings any class into one of two diagonal shapes. On classes whose
determinant is coprime to $`N` the fixing follows from the coprime-determinant injectivity
{bpref "shimura-prop-3-31"}[], comparing with the full-level transpose double coset, which is
invariant because a diagonal matrix is its own transpose; on the remaining bad classes the
representative may be taken to be $`\mathrm{diag}(1,m)`, again fixed by the conjugated transpose.
Hence every double coset is preserved, and {bpref "mul-comm-of-ai"}[] yields commutativity of
$`R(\Gamma_0(N),\Delta_0(N))` \[Sh, §3.3, Prop 3.8\].
:::

:::theorem "shimura-thm-3-35" (lean := "HeckeRing.GLn.shimura_thm_3_35")
*The level-comparison surjection $`R(\Gamma,\Delta)\to R(\Gamma_0(N),\Delta_0(N))`.*
Write $`\Gamma = SL_2(\mathbb{Z})` and let $`\Delta` be the monoid of integral matrices of positive
determinant, so that $`R(\Gamma,\Delta)` is the full $`\mathrm{GL}_2` Hecke ring. There exists a
ring homomorphism
$$`
  \varphi\;\colon\;R(\Gamma,\Delta)\;\longrightarrow\;R(\Gamma_0(N),\Delta_0(N))
`
to the congruence Hecke ring of level $`N`, and this homomorphism is surjective. Thus every element
of the level-$`N` Hecke ring is the image of a full-level Hecke operator, so the comparison from full
level down to level $`N` exhausts the congruence ring \[Sh, Thm 3.35\].

Depends on: {uses "gamma0-pair"}[] {uses "hecke-ring"}[] {uses "shimura-prop-3-31"}[] {uses "T-bad-mul"}[]
:::

:::proof "shimura-thm-3-35"
The construction goes through the polynomial presentation of the full Hecke ring. Over the prime
generators $`X_{(p,0)}, X_{(p,1)}` there is a surjection $`\pi\colon\mathbb{Z}[X_{(p,k)}]\to
R(\Gamma,\Delta)` sending each generator to the corresponding prime-power Hecke class; surjectivity
follows by splitting an arbitrary diagonal class into its prime components and inducting on the
product of the entries. Define a second homomorphism $`\psi\colon\mathbb{Z}[X_{(p,k)}]\to
R(\Gamma_0(N),\Delta_0(N))` on the same generators by sending $`X_{(p,0)}` to the class of
$`\mathrm{diag}(1,p)`, sending $`X_{(p,1)}` to the class of $`\mathrm{diag}(p,p)` when $`p\nmid N`,
and sending it to $`0` otherwise. Because the prime-power generators are algebraically independent,
$`\pi` is injective, so its kernel is trivial and in particular contained in the kernel of $`\psi`.
The universal property of the quotient then factors $`\psi` through the isomorphism
$`\mathbb{Z}[X_{(p,k)}]/\ker\pi\cong R(\Gamma,\Delta)`, producing the desired homomorphism
$`\varphi` with $`\varphi\circ\pi=\psi`.

It remains to prove $`\varphi` surjective, for which it suffices that $`\psi` already hits every
basis class of $`R(\Gamma_0(N),\Delta_0(N))`. Every double coset of $`\Gamma_0(N)` admits a diagonal
representative $`\mathrm{diag}(a_0,a_1)` with $`a_0\mid a_1` and $`\gcd(a_0,N)=1`, obtained by
clearing the content of an integral representative and reducing the primitive part to upper-triangular
diagonal form. Splitting off this content factors the class as a scalar class of
$`\mathrm{diag}(a_0,a_0)` times the primitive class of $`\mathrm{diag}(1,a_1/a_0)`. The primitive
classes $`\mathrm{diag}(1,m)` lie in the range of $`\psi` because the multiplicativity of the bad
classes {bpref "T-bad-mul"}[] together with the coprime-determinant identification of level-$`N`
cosets {bpref "shimura-prop-3-31"}[] reduces each to a product of the prime images of $`\psi`;
the scalar classes are images of the corresponding squares of those generators. Hence every basis
class is in the range, $`\psi` is surjective, and therefore so is the induced map $`\varphi`,
completing the proof of Shimura's Theorem 3.35.
:::
