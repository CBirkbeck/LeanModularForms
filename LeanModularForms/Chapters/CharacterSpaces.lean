import Verso
import VersoManual
import VersoBlueprint
import LeanModularForms.HeckeRIngs.GL2.CharacterDecomp
import LeanModularForms.HeckeRIngs.GL2.Unified.NebentypusHeckeRingHom

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Character spaces and the diamond decomposition" =>

For each unit $`d` modulo $`N` the diamond operator $`\langle d\rangle` acts on the modular forms of level
$`\Gamma_1(N)` and weight $`k`, and these operators assemble into an action of the finite abelian group
$`(\mathbb{Z}/N\mathbb{Z})^\times` on the complex vector space $`M_k(\Gamma_1(N))`. Because the group is
finite abelian and $`\mathbb{C}` contains all roots of unity, this representation is simultaneously
diagonalisable, and the space splits as the direct sum, over the Dirichlet characters $`\chi` modulo $`N`,
of the Nebentypus eigenspaces $`M_k(N,\chi)`. Each summand is preserved by the congruence Hecke ring, so the
whole Hecke action respects the diamond decomposition and may be studied one character at a time. This is the
character-space decomposition of \[DS, §5.2\].

:::theorem "charSpace-directSum" (lean := "HeckeRing.GL2.ModularForm_Gamma1_charSpace_directSum")
*Diamond decomposition into Nebentypus spaces.*
Fix a positive integer $`N` and a weight $`k`. The diamond operators $`\langle d\rangle` for $`d` a unit
modulo $`N` give an action of the finite abelian group $`(\mathbb{Z}/N\mathbb{Z})^\times` on the space
$`M_k(\Gamma_1(N))` of modular forms of level $`\Gamma_1(N)` and weight $`k`. Indexing by the group of
Dirichlet characters $`\chi` modulo $`N`, the family of Nebentypus spaces $`M_k(N,\chi)` realises
$`M_k(\Gamma_1(N))` as their internal direct sum:
$$`
  M_k(\Gamma_1(N)) \;=\; \bigoplus_{\chi} M_k(N,\chi).
`
Equivalently, the spaces $`M_k(N,\chi)` are independent and together span $`M_k(\Gamma_1(N))`, so every
modular form of level $`\Gamma_1(N)` is uniquely a finite sum of forms carrying a single Nebentypus
character.

Depends on: {uses "modFormCharSpace"}[]
:::

:::proof "charSpace-directSum"
The diamond operators define a homomorphism from the finite abelian group $`(\mathbb{Z}/N\mathbb{Z})^\times`
into the endomorphisms of $`M_k(\Gamma_1(N))`, so each $`\langle d\rangle` has finite order. Over
$`\mathbb{C}` a finite-order operator is diagonalisable, and operators coming from a commutative group
commute with one another; hence the $`\langle d\rangle` form a commuting family of diagonalisable operators on
the finite-dimensional space $`M_k(\Gamma_1(N))`. Such a family can be simultaneously diagonalised: the space
is the direct sum of the joint eigenspaces, where on each summand every $`\langle d\rangle` acts as a single
scalar $`\lambda_d`. This already shows that the joint eigenspaces are independent and that their supremum is
the whole space.

It remains to identify the indexing. A nonzero joint eigenvector with eigenvalues $`\lambda_d` forces the
assignment $`d\mapsto\lambda_d` to be multiplicative and to send $`1` to $`1`, since the diamond operators
respect the group law; as each $`\lambda_d` is a root of unity, this assignment is exactly a Dirichlet
character $`\chi` modulo $`N`. Any system of eigenvalues that is not a character contributes only the zero
space, so the nontrivial joint eigenspaces are precisely the Nebentypus spaces $`M_k(N,\chi)`, one for each
Dirichlet character $`\chi` modulo $`N`. Reindexing the simultaneous diagonalisation over the character group
therefore exhibits $`M_k(\Gamma_1(N))` as the internal direct sum of the $`M_k(N,\chi)`.

Uses: {uses "modFormCharSpace"}[]
:::

:::theorem "charSpace-iSupIndep" (lean := "HeckeRing.GL2.CuspForm_Gamma1_iSupIndep_charSpace")
*Independence of the cusp-form Nebentypus spaces.*
Fix a positive integer $`N` and a weight $`k`, and let the diamond operators $`\langle d\rangle` for $`d`
a unit modulo $`N` act on the space $`S_k(\Gamma_1(N))` of cusp forms of level $`\Gamma_1(N)` and weight
$`k`. For each Dirichlet character $`\chi` modulo $`N` write $`S_k(N,\chi)` for the cusp forms on which
every $`\langle d\rangle` acts by the scalar $`\chi(d)`. Then the family of spaces $`S_k(N,\chi)`, indexed by
the characters $`\chi`, is *independent*: each $`S_k(N,\chi)` meets the span of all the others trivially,
$$`
  S_k(N,\chi) \;\cap\; \Bigl(\sum_{\psi \neq \chi} S_k(N,\psi)\Bigr) \;=\; 0.
`
Equivalently, a cusp form that is a sum of forms carrying single, pairwise-distinct Nebentypus characters
vanishes only when each summand does. This is the cusp-form counterpart of the diamond decomposition
{bpref "charSpace-directSum"}[]; together with the fact that the $`S_k(N,\chi)` span $`S_k(\Gamma_1(N))`,
it exhibits $`S_k(\Gamma_1(N))` as the internal direct sum of the $`S_k(N,\chi)`.

Depends on: {uses "modFormCharSpace"}[]
:::

:::proof "charSpace-iSupIndep"
The diamond operators on $`S_k(\Gamma_1(N))` form a commuting family: they are the images, under a single
monoid homomorphism from the abelian group $`(\mathbb{Z}/N\mathbb{Z})^\times`, of commuting group elements.
Each $`\langle d\rangle` has finite order, so over $`\mathbb{C}` it is diagonalisable, with the whole space
the sum of its eigenspaces. For a commuting family of diagonalisable operators on a finite-dimensional space
the joint eigenspaces are independent: a relation among nonzero vectors lying in joint eigenspaces with
distinct eigenvalue systems must be trivial, because two distinct eigenvalues of one operator have disjoint
eigenspaces. This is the operator-theoretic incarnation of the orthogonality of distinct characters.

Finally, distinct Dirichlet characters $`\chi \neq \psi` differ at some unit $`d`, so they assign different
scalars to $`\langle d\rangle` and hence pick out joint eigenspaces with distinct eigenvalue systems.
Restricting the independence of all joint eigenspaces along the injection of characters into eigenvalue
systems yields the independence of the cusp-form Nebentypus spaces $`S_k(N,\chi)`.

Uses: {uses "modFormCharSpace"}[]
:::

:::definition "heckeRingHomCharSpace" (lean := "HeckeRing.GL2.Unified.heckeRingHomCharSpace")
*The Hecke ring action on a Nebentypus space.*
Fix a positive integer $`N`, a weight $`k`, and a Dirichlet character $`\chi` modulo $`N`. The congruence
Hecke ring $`R(\Gamma_0(N),\Delta_0(N))` of the pair $`(\Gamma_0(N),\Delta_0(N))`, with $`\mathbb{Z}`
coefficients, acts on the Nebentypus space $`M_k(N,\chi)` by a ring homomorphism
$$`
  \Phi_\chi \colon R(\Gamma_0(N),\Delta_0(N)) \longrightarrow \operatorname{End}_{\mathbb{C}} M_k(N,\chi),
`
into the ring of $`\mathbb{C}`-linear endomorphisms of the eigenspace.

The action of a basis double coset $`\Gamma_0(N)\,\alpha\,\Gamma_0(N)` is the $`\chi`-twisted Hecke
operator: decomposing the double coset into finitely many left cosets $`\Gamma_0(N)\,\alpha_i`, a form $`f`
is sent to the weight-$`k` weighted sum of its slashes $`f\mid_k \alpha_i`, each summand twisted by the value
of $`\chi` on the relevant unit so that the result again carries the Nebentypus character $`\chi`. This
twisted slash preserves $`M_k(N,\chi)`, packages as a $`\mathbb{C}`-linear endomorphism, and extends
$`\mathbb{Z}`-linearly over the whole ring; the ring-homomorphism axioms are transported from the
corresponding identities for the operators acting on the underlying functions on the upper half-plane, using
that the coercion $`M_k(N,\chi)\hookrightarrow(\mathcal{H}\to\mathbb{C})` is injective.

On the standard generators at a good prime $`p\nmid N` the map is explicit: the prime double coset
$`\Gamma_0(N)\,\mathrm{diag}(1,p)\,\Gamma_0(N)` is sent to $`\chi(p)^{-1}` times the usual Hecke operator
$`T_p`, while the scalar double coset $`\Gamma_0(N)\,\mathrm{diag}(p,p)\,\Gamma_0(N)` is sent to the scalar
$`\chi(p)^{-1}\,p^{\,k-2}`. Because the source ring is commutative, all the resulting operators on
$`M_k(N,\chi)` commute.

Depends on: {uses "modFormCharSpace"}[] {uses "gamma0-pair"}[]
:::
