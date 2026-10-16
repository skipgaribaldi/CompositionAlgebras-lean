# Composition Algebras in Lean 4

This project provides mathlib-like support for **composition algebras**, which
are currently missing from mathlib. This development requires **Witt cancellation for quadratic
forms** and **Artin's theorem on alternative rings**, so we include those also. Both are absent
from mathlib and both are of interest well beyond composition algebras — see
[Results of independent interest](#results-of-independent-interest).

The proofs of these results are known to work not only over fields but also over some rings
(such as semilocal rings), so we work in that same level of generality. The proofs over fields
go through with almost no changes in the setting of **LG rings**, a class of commutative rings
which includes semilocal rings, so that is the generality where we work.

> **Motto.** LG rings are the class of commutative rings where most results of undergraduate
> linear algebra for vector spaces also hold for projective modules.

This repository is a standalone Lean 4 package, distributed the way one might distribute the
Lean code supporting a paper. It is **not** self-contained: it depends on
[mathlib](https://github.com/leanprover-community/mathlib4) and treats mathlib as the canonical
library, in much the same way the [Tau Ceti](https://github.com/TauCetiProject/TauCeti) project
does. We reuse mathlib's definitions wherever they exist and reinvent nothing that mathlib
already has. Where our conventions must differ from mathlib's, we say so loudly and explain why
(see [Boundaries and traps](#boundaries-and-traps)).

Companion documents:

- [`RESULTS.md`](RESULTS.md) — the detailed record of what is proved, indexed by its citation in
  `GPR`, `GN`, `EKM` and `Dias`, with the Lean names that prove it.
- [`AGENTS.md`](AGENTS.md) — conventions for writing and organizing the Lean code. Read it before
  contributing.

---

## Table of contents

- [Why LG rings](#why-lg-rings)
- [Results of independent interest](#results-of-independent-interest)
- [What this repository contains](#what-this-repository-contains)
- [Relationship to mathlib](#relationship-to-mathlib)
- [Mathematical contents, layer by layer](#mathematical-contents-layer-by-layer)
- [Design decisions](#design-decisions)
- [Boundaries and traps](#boundaries-and-traps)
- [References](#references)
- [Status](#status)
- [Building](#building)

---

## Why LG rings

A **composition algebra** over a commutative ring `k` is a unital (not necessarily associative)
`k`-algebra equipped with a quadratic norm form `n` satisfying `n(xy) = n(x)n(y)`, subject to
regularity conditions. Over a field these are exactly `k`, the quadratic étale algebras, the
quaternion algebras, and the octonion algebras — dimensions 1, 2, 4, 8 — and they are classified
by their norm forms.

Almost all of that survives verbatim over a commutative ring **provided** the ring is nice
enough that finitely generated projective modules behave like vector spaces. The class that
isolates exactly this is the class of **LG (local–global) rings**:

> A commutative ring `R` is an **LG ring** if for every `n` and every polynomial
> `f ∈ R[X₁,…,Xₙ]`, `f` represents a unit over `R` if and only if `f` represents a unit over
> every residue field `R/𝔪`.

LG rings include all fields, all semilocal rings (hence all local and all Artinian rings), all
zero-dimensional rings, and the ring of all algebraic integers `ℤ̄`. They do **not** include `ℤ`
or `R[t]` for `R` an integral domain. Two consequences drive everything here:

1. **Constant-rank projective ⇒ free.** Over an LG ring, a finitely generated projective module
   of constant rank is free. This is the precise sense in which the motto holds.
2. **Witt cancellation.** Quadratic forms over an LG ring cancel: `q₁ ⊥ q₃ ≅ q₂ ⊥ q₃ ⟹ q₁ ≅ q₂`
   (with the hypotheses recorded in the layer description below).

These two facts are what let the field-case proofs of the composition-algebra theory run
unchanged. Working at this level of generality costs us almost nothing in proof complexity and
buys a substantially more useful theorem set.

---

## Results of independent interest

Some of what this repository proves is needed for composition algebras but is not *about* them.
Each item below is (a) developed here, (b) absent from mathlib, and (c) likely to be wanted by
people with no interest in octonions. They are written to be liftable: the files containing them
import mathlib only, and nothing composition-algebra-specific (see
[Relationship to mathlib](#relationship-to-mathlib) and `AGENTS.md` §3).

- **Witt cancellation for quadratic forms.** Over a field this is classical and belongs in any
  quadratic-forms library; mathlib has `QuadraticMap`, `IsometryEquiv` and orthogonal sums but no
  cancellation theorem. We prove it over LG rings — for `q₂` nonsingular and `q₃` regular,
  `q₁ ⊥ q₃ ≅ q₂ ⊥ q₃ ⟹ q₁ ≅ q₂` — with the field case obtained by passing `isLGRing_of_field`.
  Anyone working with quadratic forms over rings or fields wants this. *(Layer 0.)*

- **Artin's theorem on alternative rings.** *A non-associative ring is alternative if and only if
  every subring generated by two elements is associative.* This is the fundamental structural fact
  about alternative rings — it is what makes them tractable at all, and it yields
  power-associativity, diassociativity, and the well-behavedness of inverses as corollaries. mathlib
  has the non-associative hierarchy (`NonUnitalNonAssocRing` and friends) and Jordan rings
  (`IsJordan`), but **no alternative rings at all**: no `IsAlternative`, no Moufang identities, no
  Artin. Anyone interested in Moufang loops, Jordan and alternative algebra generally, or the
  nonassociative side of ring theory needs this material and would otherwise have to build it from
  scratch. Along the way we prove the alternating property of the associator
  (characteristic-2-safe), the three **Moufang identities**, and relative nuclearity
  (`IsNuclearIn`), building on mathlib's associator and its Teichmüller identity
  (`associator_cocycle`). *(Layers 1–4.)*

- **LG (local–global) rings.** The `IsLGRing` predicate with its examples (fields, semilocal rings,
  zero-dimensional rings, products of fields, direct limits) and non-examples (`ℤ`, `R[X]`), and the
  theorem that a finitely generated projective module of constant rank over an LG ring is free. That
  last result is a statement about modules that anyone doing commutative algebra might want, and it
  currently has no home in mathlib. *(Layer 0.)*

- **The rank decomposition of a finitely generated projective module** (`GPR Exc. 9.31`). A f.g.
  projective module takes finitely many ranks, and the base ring splits uniquely into a product of
  rings on each factor of which the module has constant rank. Nothing here is about composition
  algebras — it is commutative algebra that mathlib has all the ingredients for but has not
  assembled, including the module analogue of `CompleteOrthogonalIdempotents.bijective_pi`.
  *(Layer 0.)*

- **Invertible modules are line bundles.** An `R`-module is invertible in mathlib's sense precisely
  when it is finite projective and has rank one at every stalk
  (`Module.invertible_iff_isLocallyFreeRankOne`). This supplies the characterization still listed
  as a TODO in mathlib's `PicardGroup.lean`, and implies the rank-one evaluation-pairing identity
  used by the twisted-matrix construction. *(Layer 0.)*

- **Isotropy of quadratic forms over a finite field.** *Over a finite field every quadratic form
  in more than two variables has a nonzero null vector* — Chevalley–Warning applied to the
  degree-two polynomial of the form. mathlib has Chevalley–Warning as a statement about
  multivariate polynomials but nothing connecting it to `QuadraticForm`; the bridge is
  `QuadraticForm.toMvPolynomial` together with the new bound
  `QuadraticForm.totalDegree_toMvPolynomial_le`. *(Layer 11.)*

- **Anisotropic real quadratic forms are classified by their dimension and sign.** mathlib has both
  halves of Sylvester's law of inertia — a real quadratic form is a weighted sum of squares with
  weights `-1, 0, 1` (`QuadraticForm.equivalent_one_zero_neg_one_weighted_sum_squared`), and the
  numbers of positive and negative weights are invariants (`QuadraticForm.sigPos`,
  `QuadraticForm.sigNeg`) — but not the consequence that an anisotropic real form taking a positive
  value is the sum of `dim` squares, hence positive definite, hence determined up to isometry by its
  dimension. *(Layer 11.)*

⚠ Of these, Artin's theorem is the one where the hard direction is a genuinely substantial
formalization — a multi-page argument in Schafer and Zhevlakov, not previously formalized in Lean
as far as we know. See [Status](#status) for what is actually proved.

---

## What this repository contains

Four bodies of material, in dependency order:

1. **LG rings and quadratic-form foundations.** The `IsLGRing` predicate, its examples and
   non-examples, constant-rank projective ⇒ free, the representation lemma, and **Witt
   cancellation**. Much of this is of independent interest and has no composition algebras in it —
   see [Results of independent interest](#results-of-independent-interest).
2. **Alternative algebras.** Associators and the Teichmüller identity (both from mathlib:
   `associator`, `associator_cocycle`), relative nuclearity, the `IsAlternative` predicate, the
   Moufang identities, and **Artin's theorem**. Prerequisite structure theory for composition
   algebras, and the largest block here that is of independent interest — mathlib has no alternative
   rings at all.
3. **Conic and composition algebras.** The conic-algebra structure (norm, trace, conjugation),
   the Cayley–Dickson doubling construction, composition algebras, octonions, worked examples and
   non-examples.
4. **Classification.** The norm form determines the algebra (over LG rings); reduced composition
   algebras and their structure; classification over special classes of fields.

---

## Relationship to mathlib

mathlib is canonical. Concretely:

**We consume, and never re-define:**

- The non-associative algebraic hierarchy: `NonUnitalNonAssocRing`, `NonAssocRing`,
  `NonUnitalNonAssocSemiring`, `NonUnitalNonAssocAlgebra`, `NonUnitalAlgHom`, `AlgEquiv`,
  `MulOpposite`.
- Quadratic and bilinear forms: `QuadraticMap`, `QuadraticForm`, `QuadraticMap.polar`,
  `QuadraticForm.polarBilin`, `QuadraticMap.Anisotropic`, `QuadraticMap.IsometryEquiv`,
  `QuadraticForm.baseChange`, `QuadraticForm.dualProd` (the hyperbolic form, with its isometries
  `dualProdIsometry` and `dualProdProdIsometry`), `LinearMap.BilinForm` and `.Nondegenerate`.
- Modules: `Module.Free`, `Module.Finite`, `Module.Projective`, `Module.rank`, `Module.finrank`,
  `Basis`, `Module.Dual`, `Module.IsUnimodular`, `Algebra.TensorProduct`.
- Concrete algebras: `Complex`, `Quaternion` / `QuaternionAlgebra`, and `Analysis.Quaternion`
  for the real normed picture.
- Field-theoretic inputs where the classification needs them: `FieldTheory.ChevalleyWarning`,
  `LinearAlgebra.QuadraticForm.Real` (Sylvester's law of inertia), `Padics`.

**We build what mathlib lacks:** LG rings, Witt cancellation, the nonsingular/regular quadratic-form
predicates, alternative algebras, Moufang, Artin, conic algebras, Cayley–Dickson, composition
algebras, octonions, and the classification results.

**Upstreaming.** The items in [Results of independent interest](#results-of-independent-interest)
are plausible mathlib contributions on their own merits, and are written so they can be lifted out
cleanly — in rough order of readiness: alternative rings with the Moufang identities and Artin's
theorem (both directions proved); Witt cancellation over fields; LG rings together with
constant-rank-projective ⇒ free; then the conic/composition tower. The import discipline that keeps
this possible is specified in [`AGENTS.md`](AGENTS.md); the short version is that general-purpose
files must not import composition-algebra-specific ones.

---

## Mathematical contents, layer by layer

Primary reference: **GPR** = Garibaldi–Petersson–Racine, *Albert Algebras over Commutative
Rings*. Section numbers like `GPR 16.1` refer to it. **GN** = Gille–Neher, *Group schemes over
LG-rings and applications to cancellation theorems and Azumaya algebras*, European Journal of
Mathematics **11** (2025), article 42; numbering follows the **published** version.

### Layer 0 — LG rings and Witt cancellation

Foundational quadratic-form theory, absent from mathlib. Independent of everything below it.

- **Definition (`GN 2.1`).** `IsLGRing R`: for every `f ∈ R[X₁,…,Xₙ]`, `f` represents a unit over
  `R` iff it does over every residue field `R/𝔪` (equivalently over every localization `R_𝔪`;
  equivalently over every field in `R`-alg). The three formulations and their equivalence.
  Immediate consequences worth having: `GN 2.1(a)` (a finite direct product is LG iff each factor
  is) and `GN 2.1(b)` (`R` is LG ⟺ `R/Jac(R)` is LG).
- **Examples (`GN 2.2`).** The **zero ring** — *proved* (`isLGRing_of_subsingleton`). Every
  field. Every **semilocal** ring — the workhorse instance, via `GN 2.1(a)`/`2.1(b)`: `R/Jac(R)` is
  a finite product of fields — hence every local, Artinian, and finite ring. The ring of **all
  algebraic integers** `ℤ̄` (and of all real algebraic integers), via the primitive criterion of
  `GN 2.2(e)`: every primitive polynomial represents a unit, which holds exactly when the ring is LG
  **and** has no finite residue fields (`ℤ̄` has no finite non-zero homomorphic images). ⚠ Infinite
  residue fields alone do not make a ring LG: `ℚ[t]` is a counterexample, by the non-examples below.
  *Not formalized*: neither the criterion nor the LG property of `ℤ̄` is proved here. Also *proved*:
  `R` with `R/Jac(R)` **von Neumann regular** (`GN 2.2(c)`,
  `isLGRing_of_isVonNeumannRegular_quotient_jacobson`); **zero-dimensional** rings (`GN 2.2(d)`,
  `isLGRing_of_krullDimLE_zero`); **direct limits** (`isLGRing_directLimit`, with the directed-union
  form `isLGRing_of_directed_subring`); arbitrary **products of fields** `∏ᵢ Kᵢ`, in particular
  `F^I` (`isLGRing_pi_of_forall_field`, `isLGRing_pi_field`). Still open: closure under integral
  extensions (`GN 2.2(b)`) and the criterion `GN 2.2(e)`, hence `ℤ̄`. All of these run through one
  finitary reformulation of the axiom (`isLGRing_iff_forall_valueIdeal_eq_top`,
  `LGRing/ValueIdeal.lean`): `R` is LG iff every `p` whose *values* generate the unit ideal takes a
  unit value. That hypothesis unwinds to a single equation `1 = Σⱼ cⱼ · p(tⱼ)` in finitely many
  elements of `R`, which is what survives a filtered colimit and what the idempotent block
  decomposition in `LGRing/ZeroDimensional.lean` glues along.
- **Non-examples (`GN 2.2(f)`, `GPR Exc. 11.42`).** `ℤ` is **not** LG; `R[X]` is **not** LG for `R`
  an integral domain. Both follow from one observation: over an LG ring `X² + r` represents a unit
  for every `r ∈ R`. Cheap, high-value negative results — they stop `IsLGRing` being silently
  assumed for the most familiar bases, and mark exactly where the classification stops. Note the
  contrast: `ℤ` is not LG but `ℤ̄` is (`GN 2.2(e)`, not formalized here).
- **Geometric characterization (`GN 2.3`, `GN Prop. 2.4`).** For `M` finite locally free over an LG
  ring and `U ⊆ W(M)` open quasi-compact, `U(R) ≠ ∅ ⟺ U(R/𝔪) ≠ ∅` for every maximal `𝔪`. This
  *characterizes* LG rings and is the form in which the LG axiom is actually applied. Optional for
  our purposes — the composition-algebra results can be reached without the scheme language — but
  it is the conceptually right statement and worth recording even if not formalized.
- **Unimodular elements and constant-rank projectives (`GN 2.5`–`2.6`, `GPR 11.24`).** `m ∈ M` is
  **unimodular** if some linear functional takes the value `1` at `m` — mathlib's
  `Module.IsUnimodular`, which we use — equivalently if `R·m` is free of rank 1 and a direct
  summand of `M`, which is the definition in `GPR 9.13`. When `M` is finitely generated projective
  this is also equivalent to `m ⊗ 1_{κ(𝔭)} ≠ 0` for every `𝔭 ∈ Spec R` (`GPR 9.17`). ⚠ Not in
  general: in the `ℤ`-module `ℤ ⊕ ℤ/2` the element `(2, 1̄)` survives in every residue field but no
  functional takes it to `1` (`Module/Unimodular.lean`). Then: over an LG
  ring a **faithfully projective** module contains a unimodular element (`GN 2.6(a)`), and a finite
  projective module of **constant rank is free** (`GN 2.6(b)`, also stated in `GN 2.1(c)`) — the
  motto, made precise — whence `Pic(R) = 0` (`GN (2.1.1)`). *Both are formalized*: 2.6(a) in
  `LGRing/Unimodular.lean`, by an elementary argument that stays inside the polynomial form of the
  LG axiom rather than following `GN`'s scheme-theoretic route, and 2.6(b) in
  `LGRing/ConstantRank.lean`, by induction on mathlib's `Module.rankAtStalk`.
- **Representation lemma (`GPR 11.26`; `GN Lemma C.13(a)`).** Over an LG ring, a quadratic space
  `(M, q)` represents a unit — `q(M) ∩ Rˣ ≠ ∅` — iff `M` is faithfully projective (equivalently,
  has full support). `GPR 11.26` states it for `q` **regular**; `GN C.13(a)` observes the same proof
  gives the **nonsingular** case. This is the bridge from the LG axiom to the structure theory: it
  is what produces the scalar `μ ∈ kˣ` to double by in the Cayley–Dickson structure theorem.
  *Formalized* (`QuadraticForm/Representation.lean`), in both directions and with no freeness or
  constant-rank hypothesis: pulling `q` back along a presentation `Rⁿ ↠ M` supplies the basis that
  `GPR 11.8` needs, so the reduction to constant rank that `GPR` and `GN` use is unnecessary.
- **Witt cancellation (`GN 6.5`; cf. `GPR 11.27`).** Over an LG ring, for `q₁, q₂` **nonsingular**
  and `q₃` **regular**, `q₁ ⊥ q₃ ≅ q₂ ⊥ q₃ ⟹ q₁ ≅ q₂`. The hypothesis asymmetry is essential:
  cancellation is **false** if all three are merely nonsingular (counterexample: EKM p. 49).
  `GPR 11.27` states the weaker all-regular version (GPR's "quadratic space" means regular);
  `GN 6.5` subsumes it. Over a field this is classical Witt cancellation, recovered by passing
  `isLGRing_of_field`. The LG-ring case for regular forms is originally Dias (thesis, II.6.4),
  following Baeza and Knebusch; `GN 6.5` is proved cohomologically (see the ⚠ in `AGENTS.md` §8).
  *Formalized* (`QuadraticForm.cancel`, `QuadraticForm/WittCancellation.lean`) by the Dias route.

### Layer 1 — Associator, nucleus, center

`associator x y z = (x * y) * z - x * (y * z)` on a `NonUnitalNonAssocRing` is mathlib's; this layer
adds its additivity API. The center is mathlib's (`NonUnitalSubring.center`, built on
`IsMulCentral`, which includes the associativity conditions), and mathlib already proves it
commutative. *Not yet formalized* (TODO in `Nonassociative/Associator.lean`): the associator bundled
trilinearly over an algebra, and the left/middle/right nuclei as associative sub-structures. Artin's
theorem needs only nuclearity relative to a subset, `IsNuclearIn` (`Alternative/Artin.lean`), which
is formalized.

### Layer 2 — Alternative algebras

`IsAlternative`: `associator x x y = 0` and `associator x y y = 0`. The linearizations give
**alternation of the associator** (it changes sign under transposition of adjacent arguments) —
proved with additivity only, hence valid in characteristic 2. Flexibility follows.

### Layer 3 — Moufang identities

For unital alternative rings: the left, right, and middle Moufang identities, and their
equivalence. Diassociativity helpers and power-associativity of two-generated subrings.

### Layer 4 — Artin's theorem

A unital ring is alternative iff every pair of elements generates an associative subring. The
forward direction uses Moufang plus associator alternation; the converse is immediate. Corollaries:
diassociativity, power-associativity, and the inverse lemmas used for division algebras.

### Layer 5 — Conic algebras (`GPR 16.1`)

A **conic algebra** over `k`: a unital, not-necessarily-associative `k`-algebra with a chosen
quadratic norm `n` satisfying `n(1) = 1` and the degree-2 identity `x² − n(1,x)·x + n(x)·1 = 0`.
The norm is **data** (it need not be unique). No regularity, no projectivity.
On a finitely generated projective algebra it becomes unique (`GPR 16.16`,
`ConicAlgebra.norm_eq_of_projective`).

Trace and conjugation are derived from the **un-halved polar form**: `t(x) = polar n 1 x` (so
`t(1) = 2`) and `x̄ = t(x)·1 − x`. Core identities: conjugation is a linear involution,
`x + x̄ = t(x)·1`, `x·x̄ = x̄·x = n(x)·1`, `t(x̄) = t(x)`, `n(x̄) = n(x)`, and the linearized
degree-two identity `xy + yx = t(x)·y + t(y)·x − n(x,y)·1`, which is the workhorse of the whole
conic calculus.

Conic algebras are stable under base change (the final paragraph of `GPR 16.1`). ⚠ What is
formalized here is `ConicAlgebra.baseChangeOfProjective`, which assumes the module **finitely
generated projective** — the name carries the restriction rather than hiding it. The hypothesis is
inherited from the norm: base change of a quadratic form over an arbitrary module needs quadratic
maps as degree-two polynomial laws. mathlib has the polynomial-law and divided-power infrastructure
(`PolynomialLaw`, `DividedPowerAlgebra`) but not the bridge from it to `QuadraticMap` — neither
`Γ₂(M)` as the universal quadratic map nor an identification of quadratic maps with degree-two laws
— so this repository only has base change for projective modules
(`QuadraticForm.baseChangeOfProjective`, which in exchange assumes nothing about `2`; see the TODO
in `QuadraticForm/BaseChangeProjective.lean`). Nothing in Layers 6–8 needs the general case:
composition algebras are finitely generated projective by definition, and Cayley–Dickson doubling
preserves that.

⚠ **Conjugation is *not* an anti-homomorphism merely because the algebra is alternative** — see
[Boundaries and traps](#boundaries-and-traps), trap 6. What is true in every conic algebra is the
sharp identity `ȳ x̄ = conj(xy) + (t(x)t(y) − n(x,y) − t(xy))·1` (`GPR 16.5(11)`); the scalar is the
obstruction, and `GPR 16.10(a)` says conjugation is an involution exactly when it lies in `Ann(A)`.
It vanishes for alternative algebras over a **field**, and — `GPR 16.14(b)`, `GPR 17.6` — over any
base for which the algebra is finitely generated projective, but not over an arbitrary ring.

**Division** (`GPR 8.6`, `GPR 13.8`). `IsDivision A` (`Nonassociative/Division.lean`) is `GPR`'s
notion: `A ≠ 0`, and multiplication on either side by a nonzero element is bijective. Over a field,
`x x̄ = n(x)·1` gives every nonzero element of an anisotropic conic algebra the two-sided inverse
`n(x)⁻¹ x̄`. ⚠ That property, `ConicAlgebra.HasTwoSidedInverses`, is weaker than division: the real
sedenions have such inverses and also zero divisors (`GPR Exc. 19.29(e)`). For an *alternative*
conic algebra over a field, division, two-sided inverses and anisotropy of the norm all coincide
once `A ≠ 0` (`Conic/Division.lean`), by the identities `x̄(xy) = n(x)y = (yx)x̄`.

### Layer 6 — Cayley–Dickson doubling (`GPR 18.3–18.6`)

`Cay(B, μ)` on `B × B` with `(u₁,v₁)(u₂,v₂) = (u₁u₂ + μ·v̄₂v₁, v₂u₁ + v₁ū₂)`, unit `(1,0)`, norm
`n_B ⊥ ⟨−μ⟩n_B`, conjugation `(u,v) ↦ (ū, −v)`. *Formalized* (`Conic/CayleyDickson.lean`):
`ConicAlgebra.cay` is `GPR 18.4`, with no hypothesis on `B` or on `μ`.

**The scalar `μ` is an arbitrary element of `k`, not a unit.** The construction and its conic
structure hold for every `μ`; unit hypotheses appear only on later theorems. Rank doubles. The
external construction (on `B × B`) is preferred over the internal `B + Bj`, which can fail to be
a direct sum.

Property propagation (`GPR 18.11–18.15`, `Exc. 18.18`): involutivity of conjugation passes from
`B` to `Cay(B, μ)`. The double is commutative iff `B` is commutative with trivial conjugation;
associative iff `B` is commutative associative with involutive conjugation; and alternative iff
`B` is associative with involutive conjugation. The repository proves that an associative
multiplicative `B` has a multiplicative double, and conversely that a multiplicative double has
multiplicative `B`; the sharper criterion of `GPR Exc. 18.18` is not yet formalized. Base change
is compatible with doubling.

### Layer 7 — Composition algebras (`GPR 19.5`)

A **composition algebra**: a conic algebra that is **finitely generated** projective, with a
**non-singular** multiplicative norm. Non-singularity is the base-change-stable regularity
condition, and is the one new form-regularity predicate we build.

⚠ This is very slightly less general than `GPR 19.5`, which assumes only projective of locally
constant rank — allowing the rank to be infinite a priori — and then *proves* it finite, indeed one
of `1, 2, 4, 8` (`GPR 19.18`). We assume finite generation outright, so the two definitions pick out
the same objects only a posteriori: ours builds in a conclusion of the theory rather than deriving
it, so "every composition algebra" means the finitely generated ones. `GPR 19.18` is now proved
(`Composition/RankOneTwoFourEight.lean`), but for *our* definition — it says a finitely generated
composition algebra of constant rank has rank `1, 2, 4, 8`, which is not yet the derivation of
finiteness that would close the gap. Conversely, no *locally constant rank* clause is needed: that
is automatic for a finitely generated projective module. It is the **constancy** of the rank that
later theorems assume, as a hypothesis on those theorems.

⚠ Get the definition right (`GN C.8(d),(e)`): the **radical** of a quadratic form is
`rad(q) = {m ∈ M : q(m) = 0 = b_q(m, M)}` — note it constrains `q` *and* the polar form `b_q`, not
just `b_q` — and `q` is **non-singular** iff `rad(q_F) = 0` for **every field** `F ∈ k`-alg.
(Finite projectivity of the underlying module is part of GN's definition of a quadratic form, so
it is not a separate clause.) Base change to every field is what makes the notion stable, since
`rad(q) ⊗ T ⊆ rad(q_T)` can be strict. Related facts to record: `q` regular ⇒ `q` non-singular
(`GN (C.8.1)`), the converse fails (`⟨u⟩ : r ↦ ur²` is non-singular but regular only when
`2 ∈ kˣ`), and when `2 ∈ kˣ` the two coincide (`GN (C.8.2)`). All three are proved in
`QuadraticForm/Regularity.lean`, the middle one as `QuadraticForm.rankOne`. Over a field,
non-singular agrees with EKM-nondegenerate (`GN C.9`); that identification, `EKM Lemma 7.16`, and
`GPR Exc. 11.37` are proved in `QuadraticForm/NonsingularOverFields.lean`.

- Every composition algebra is alternative (`GPR 19.3`, via Kirmse's identities).
- **Recognition (`GPR 19.3`).** A *projective* conic algebra with a *non-degenerate multiplicative*
  norm is automatically conic alternative, and that norm is the unique conic norm.
- **Doubling recognizes composition**, and conversely.
  `GPR 19.16(b)`: over an LG ring, rank > 1 forces a regular rank-2 subalgebra — **proved**
  (`Composition/RankTwoSubalgebra.lean`), over a field and then over an LG ring. This is what
  starts the tower.
  `GPR 19.16(a)`: over an **LG ring**, given a regular subalgebra `B ⊆ C` whose orthogonal
  complement has full support, orthogonal splitting plus the Layer-0 representation lemma yields
  `μ ∈ kˣ` and an embedding `Cay(B, μ) ↪ C` — **proved** (`Composition/Doubling.lean`), on top of
  `GPR 18.1` (`Conic/Doubling.lean`). Alternativity is derived from composition, not assumed.
  Iterating gives the full `GPR 19.17`: every composition algebra of rank greater than one over
  an LG ring arises from rank two by Cayley–Dickson, and from the base ring itself when `2` is a
  unit — **proved** (`Composition/Tower.lean`).
- **Rank classification (`GPR 19.18`).** **Proved in full**
  (`Composition/RankOneTwoFourEight.lean`), over any nontrivial commutative ring and with no LG
  hypothesis: rank one is the base ring; rank two is commutative associative with nontrivial
  conjugation; rank four is associative and noncommutative; and rank eight is alternative and
  nonassociative.
- **Relation to mathlib's `QuaternionAlgebra`** — see [Boundaries and traps](#boundaries-and-traps).

### Layer 8 — Examples and non-examples

- **`ℝ, ℂ, ℍ, 𝕆`.** The tower `ℂ = Cay(ℝ,−1)`, `ℍ = Cay(ℂ,−1)`, `𝕆 = Cay(ℍ,−1)`, with `ℂ` and `ℍ`
  identified with mathlib's `Complex` and `Quaternion ℝ` by `AlgEquiv`. Octonions are defined here
  (mathlib has none), kept general in `k` and then specialized. Each has anisotropic positive
  definite norm, hence — being alternative — is a division algebra in the sense of `GPR 8.6`.
- **Sedenions (`GPR 19.23`).** `Cay(𝕆, μ)`, rank 16: a **conic algebra that is not a composition
  algebra** — **proved** (`Composition/Sedenion.lean`), by both available routes. Its norm is
  still positive definite, so every nonzero sedenion has a two-sided inverse, yet it has explicit
  zero divisors and so is not a division algebra (`GPR Exc. 19.29(e)`).
- **Characteristic 2, purely inseparable (`GPR 19.4`).** For `F` of characteristic 2 and `C/F` a
  **proper** purely inseparable extension of exponent ≤ 1, `C` is a conic algebra whose norm is the
  squaring map: **anisotropic with identically zero polar form**. Not a composition algebra (the
  excluded case `C = F` is one). This is the sharp
  test that the conic API uses the un-halved polar and never assumes `2` is invertible — a conic
  definition needing `2 ∈ kˣ` could not even state this example. Anisotropic-with-zero-polar is
  impossible outside characteristic 2. **Proved** (`Composition/Inseparable.lean`), with the
  anisotropic witness `𝔽₂(t)(√t)` in `Composition/InseparableAnisotropic.lean`.
- Optional further non-example: the **sextonions** (`GPR 19.25`), multiplicative conic but with a
  radical in the polar form.

### Layer 9 — The norm form determines the algebra (`GPR 23.2–23.5`)

This layer is the front half of `GPR` §23, *Norm equivalences and isomorphisms*; Layer 11 below is
its back half. A **unital norm equivalence** is a linear equivalence preserving `1` and the norm,
and §23 is the comparison between those and algebra isomorphisms.

- **`GPR 23.4(a)`: easy direction, any commutative ring.** An algebra isomorphism of composition
  algebras induces an isometry of norm forms: the norm is intrinsic to the conic structure
  (`isometryEquivOfLinearEquiv`, on `norm_eq_of_projective`).
- **`GPR 23.3`: normalization.** Any norm similarity into an alternative multiplicative conic
  algebra can be corrected to a norm isometry preserving `1`
  (`IsMultiplicative.exists_isometryEquiv_map_one_of_similarity`).
- **`GPR 23.2`: what a unital norm equivalence preserves.** Trace, conjugation and squares
  (`trace_map_of_isometryEquiv_map_one`, `conj_map_of_isometryEquiv_map_one`,
  `map_mul_self_of_isometryEquiv_map_one`).
- **`GPR 23.4(b)`: the converse in rank two.** A unital norm equivalence out of a conic algebra
  generated by `1` and one element is automatically multiplicative, since multiplication there has
  only the structure constants `t(u)` and `n(u)` (`GPR 19.8`). Over a nontrivial LG ring, constant
  rank two supplies that hypothesis via `GPR 19.16(b)` plus the exhaustion criterion. **Proved**
  (`Composition/NormEquivalence.lean`), together with the biconditional form of `GPR 23.4`.
  ⚠ The converse genuinely needs rank two: conjugation on a quaternion algebra is a unital norm
  equivalence and an anti-automorphism.
- **`GPR 23.5`, the norm equivalence theorem: converse over LG rings.** Isometric norm forms imply
  isomorphic algebras (`IsComposition.exists_isometryEquiv_map_one_map_mul`), without a
  constant-rank hypothesis. Rank idempotents reduce the result to the constant-rank proof, which
  runs the field argument above **Witt cancellation** (Layer 0).
- **This is sharp.** Over general commutative rings `GPR 23.5` is **false** — see
  [Boundaries and traps](#boundaries-and-traps).

### Layer 10 — Reduced composition algebras (`GPR 22.9–22.19`)

- **Isotropy, GPR sense (`GPR 11.17`).** `q` is isotropic iff there is a **unimodular** `u` with
  `q(u) = 0`. This is *not* mathlib's notion; see [Boundaries and traps](#boundaries-and-traps).
  Uses mathlib's `Module.IsUnimodular` (a functional takes the value `1` at `u`), which agrees
  with the definition in `GPR 9.13` (`k·u` a free direct summand), as noted there.
- **`GPR 22.9`.** For rank > 1: reduced ⟺ contains a split quadratic étale subalgebra ⟺ norm
  isotropic ⟺ norm hyperbolic. The first three are **proved** (`Composition/Reduced/Defs.lean`),
  through the equivalent (in rank > 1, `GPR 22.7`) condition *has an elementary idempotent*.
  General rank-decomposed reducedness is `ConicAlgebra.IsReduced`
  (`Composition/Reduced/Reducedness.lean`); it imposes the elementary condition on the rank 2, 4,
  and 8 factors and correctly treats rank 1 as automatically reduced. The fourth condition is now
  **proved** in `Composition/Reduced/Hyperbolic.lean`: the Peirce-coordinate equivalence identifies
  the full norm with the hyperbolic form of `k ⊕ C₂₁`. It uses all six coordinate formulas of
  `GPR Exc. 19.35` and off-diagonal duality under regularity, and strengthens the earlier result
  that the plane `k c ⊕ k c̄` splits off orthogonally (`QuadraticForm/PlaneSplitting.lean`).
- **`GPR 22.10`.** Reduced rank-2 = split quadratic étale algebras. **Proved**
  (`Composition/Reduced/RankTwo.lean`), and for conic algebras, with no regularity or
  multiplicativity hypothesis: constant rank 2 plus an elementary idempotent makes
  `(a, b) ↦ a c + b c̄` an isomorphism `k × k ≅ A`.
- **Peirce decomposition (`GPR Exc. 14.12`, `GPR Exc. 19.35(1)–(6)`).** **Proved.** For an
  idempotent `c` in an alternative algebra, the four maps `x ↦ (cᵢx)cⱼ` are complete pairwise
  orthogonal projections and give a linear equivalence with their four ranges
  (`Nonassociative/Alternative/Peirce.lean`). For an elementary idempotent in a multiplicative conic
  alternative algebra, the diagonal components are exactly `k c₁` and `k c₂`, every element has
  Peirce coordinates, and the norm, polar, trace, and conjugation formulas are proved
  (`Composition/Reduced/Peirce.lean`). When the norm is regular, the polar pairing identifies
  `C₁₂ ≃ C₂₁*`; `GPR 19.11` supplies regularity for constant-rank composition algebras of rank other
  than one. The trace form `(x, y, z) ↦ t((xy)z)` on either off-diagonal component is also proved
  alternating, completing the final assertion of `GPR Exc. 19.35`. The Peirce multiplication rules
  from `GPR Exc. 14.12` used downstream are proved as well.
- **`GPR 22.13`** (Petersson). Reduced quaternion algebras are the `Endₖ(k ⊕ L)` for `L` a line
  bundle; split iff `L` is free. **Proved**
  (`Composition/Reduced/TwistedMatrix.lean`): `GPR 22.12`'s algebra of `L`-twisted matrices is
  built, is conic over any `L`, has non-singular (indeed hyperbolic) norm for `L` f.g. projective,
  is multiplicative — hence a composition algebra — under the rank-one pairing identity, and is
  reduced. Conversely, the lower-left Peirce component of a reduced rank-four composition algebra
  is a line bundle, and the Peirce coordinates give a unital multiplicative norm isometry from its
  twisted-matrix algebra onto the original algebra.
- **`GPR 22.15`** (Petersson). Reduced octonion algebras are the twisted **Zorn vector matrix**
  algebras `Zor(M, θ)`, `M` projective of rank 3 with an orientation `θ`; split iff `M` is free. The
  split form `Zor(k)` is `GPR 21.18`: elements `[[ρ₁, u₂], [u₁, ρ₂]]` with `ρᵢ ∈ k`, `uᵢ ∈ k³`,
  multiplication from dot and cross products, norm `ρ₁ρ₂ + u₁ᵀu₂`, trace `ρ₁ + ρ₂`. `Zor(k)` is
  **proved** (`Composition/Reduced/Zorn.lean`): conic, alternative, multiplicative, non-singular, of
  rank 8 — a composition algebra over *any* commutative ring, with no hypothesis on `2`. The twisted
  form is now built as `ConicAlgebra.TwistedZor` (`Composition/Reduced/TwistedZorn.lean`), on the
  data `GPR 22.14` actually consumes: a `Module.VectorProductPair` — the two associated vector
  products `M × M → M*` and `M* × M* → M`, alternating, orthogonal to their own arguments, and
  linked by Binet–Cauchy. It is conic with no hypothesis on `M`, has hyperbolic (hence regular and
  non-singular) norm for `M` finitely generated projective, is multiplicative, alternative, and
  reduced. Alternativity follows from Kirmse's theorem because regularity forces the radical to
  vanish, with no hypothesis on `2`. The orientation construction is **proved over every commutative
  ring** (`Composition/Reduced/Orientation.lean`). It localizes a constant-rank-three finite
  projective module at each maximal ideal, uses projective dual base change (`GPR 9.15`) and
  exterior-power duality (`GPR 21.7`) to show that the local primal and dual volume coefficients are
  inverse, applies the based Binet–Cauchy calculation, and descends the resulting scalar identity.
  The converse structure theorem is **proved on vector-product-pair data**
  (`Composition/Reduced/RankEight.lean`): multiplication on the two off-diagonal Peirce components
  supplies a pair, and the Peirce coordinates give a unital multiplicative norm isometry from its
  twisted Zorn algebra onto every reduced constant-rank-eight composition algebra. The twisting
  module has constant rank three. `Module.VectorProductPair.ofBasis` supplies the free case, and
  every vector-product pair on a based rank-three module is the pair of a suitably rescaled basis.
  Thus a free twisting module gives exactly `Zor(k)` and satisfies `IsSplitOfRank 8`, without a
  hypothesis on `2`.
- **`GPR 21.19`, the split models.** The four algebras splitness is defined against — `k`, `k × k`,
  `Mat₂(k)`, `Zor(k)`, of ranks 1, 2, 4, 8 — are all **proved** composition algebras over any
  commutative ring: rank 1 is `ConicAlgebra.baseRing`, ranks 2 and 4 are in
  `Composition/Reduced/Split.lean`, rank 8 in `Composition/Reduced/Zorn.lean`. **Splitness is
  defined** in `Composition/Reduced/Splitness.lean`: `IsSplitOfRank` gives the four constant-rank
  clauses, while `IsSplit` packages the composition property and applies those clauses to the base
  changes cut out by the four rank idempotents of `GPR Exc. 9.31`, exactly as in `GPR 21.19`.
- **`GPR 22.16`.** Split ⇒ reduced over any commutative ring is **proved in full** as
  `ConicAlgebra.IsSplit.isReduced`: the three standard models of rank > 1 have elementary
  idempotents, and these transport across the defining isomorphisms on the rank components. The
  converse is **proved under the factor-stable form of GPR's freeness hypothesis** as
  `ConicAlgebra.IsReduced.isSplit_of_projective_constantRank_free_on_factors`; its LG-ring
  specialization is `isSplit_of_isLGRing` (`Composition/Reduced/Classification.lean`). The rank
  decomposition gives constant rank on each idempotent factor, and freeness untwists the rank-four
  and rank-eight models.
- **`GPR 22.18`.** Over rings where constant-rank projectives are free: split ⟺ norm isotropic ⟺
  norm hyperbolic; over a field, additionally ⟺ not a division algebra. The split/isotropic
  equivalence in constant ranks two, four, and eight is **proved over nontrivial LG rings** as
  `IsComposition.isSplitOfRank_iff_isGPRIsotropic_of_isLGRing`. The hyperbolic-to-split direction is
  packaged for a hyperbolic presentation whose first module has a unimodular element; the
  reduced-to-hyperbolic presentation is `peirceHyperbolicIsometryEquiv`. The field division
  condition is **proved** as `IsComposition.isSplitOfRank_iff_not_hasTwoSidedInverses`:
  multiplicativity makes a two-sided inverse impossible for a nonzero null vector, while anisotropy
  gives the explicit inverse `n(x)⁻¹ x̄`. With division in the sense of `GPR 8.6` it is
  `IsComposition.isSplitOfRank_iff_not_isDivision`, by `GPR 13.8`.
- **`GPR 22.19`.** Over a PID, the two isotropy notions (unimodular null vector vs. represents zero)
  coincide, and both are equivalent to splitness and to having zero divisors. This is **proved** for
  constant ranks 2, 4, and 8 in `Composition/Reduced/Classification.lean`. The coordinate-ideal
  argument in `QuadraticForm/Isotropic.lean` (`GPR Exc. 12.38(c)`) divides a nonzero null vector by
  a generator of its coordinates to obtain a unimodular null vector. Projective twisting modules are
  finite free over the PID, giving splitness, while norm multiplicativity identifies anisotropy with
  mathlib's `NoZeroDivisors`. This is the one place the two isotropy notions merge.

**Capstone (`GN Example 3.15`, final paragraph, due to Garibaldi).** *Let `R` be an LG ring in
which every quadratic étale `R`-algebra is split. Then every octonion algebra over `R` is split.*
Four steps, each an earlier result: `GPR 19.16(b)` gives a regular rank-2 (quadratic étale)
subalgebra; by hypothesis it is split; by `GPR 22.9` the algebra is reduced; by `GPR 22.16` plus
constant-rank-projective ⇒ free (`GN 2.6(b)`) it is split.
This implication is **proved** in `Composition/Reduced/Capstone.lean`, with the hypothesis stated
exactly for the regular quadratic subalgebras produced by `GPR 19.16(b)`.
The instance is `R = ℤ̄`, the ring of all algebraic integers, which is LG (`GN 2.2(e)`) and simply
connected — **not** `ℤ`, which is not LG. We state the hypothesis as "every quadratic étale algebra
splits" rather than "simply connected", because that is what the proof consumes. The concrete `ℤ̄`
statement therefore needs **two** inputs from outside this development, neither formalized: that
`ℤ̄` is LG (`GN 2.2(e)`; see Layer 0), and that every quadratic étale `ℤ̄`-algebra splits.

⚠ `GN Example 3.15` gives **several** proofs of the `ℤ̄` statement — via Rumely's theorem on points
of schemes over `ℤ̄`, via strong approximation, and via `GN Cor. 3.14` (every semisimple group
scheme over `ℤ̄` is split, applied to `G₂ = Aut(𝕆)`). Only the final paragraph's argument is in
scope: it is the one whose prerequisites are all in this roadmap. Do not pursue the others.

### Layer 11 — Classification over special classes of fields (`GPR 23.12–23.22`)

Over a field every composition algebra is split or a division algebra, so classification reduces
to known facts about quadratic forms. Two mechanism theorems carry the whole layer, both in
`Composition/Fields/Basic.lean`, and every bullet below is one of them applied to a field whose
quadratic forms are understood:

- **splitting is isotropy** — `IsComposition.isSplitOfRank_iff_not_anisotropic`, the field form of
  `GPR 22.18`, with GPR's unimodular isotropy traded for mathlib's failure of anisotropy because
  the two agree over a field, and with `Module.rankAtStalk` traded for `Module.finrank`;
- **the norm is a complete invariant** — `IsComposition.isomorphic_of_isometryEquiv`, Layer 9
  applied with `isLGRing_of_field`, with
  `isomorphic_iff_nonempty_isometryEquiv` recording both directions at once.

`IsComposition.isSplitOfRank_of_forall_not_anisotropic` packages the `u`-invariant style of
argument that the finite-field and local-field bullets use, and `IsSplitOfRank.isomorphic` records
that the split algebra of a given dimension is unique.

- **Fields where every quadratic étale algebra splits** (e.g. separably closed): a unique
  composition algebra — the split one — in each dimension 2, 4, 8. **Proved**
  (`Composition/Fields/SepClosed.lean`). The conditional statement is
  `IsComposition.isSplitOfRank_of_forall_isSplit_quadraticSubalgebra`, the field case of the
  generalized capstone `isSplitOfRank_of_forall_isSplit_adjoinElement`
  (`Composition/Reduced/Capstone.lean`, now stated in every constant rank 2, 4, 8 rather than only
  8), and `isSplitOfRank_of_forall_isSplit_quadraticEtale` states it the way `GPR 23.12` does —
  quantified over *all* quadratic étale `K`-algebras, via the standalone construction of
  `Composition/QuadraticEtale.lean`. The bridge is that the subalgebra `K[u]` of `GPR 19.16(b)`
  *is* such an algebra, and that the conic structure it carries agrees with the constructed one,
  because the norm of a finite projective conic algebra is unique and a conic algebra is
  determined by its norm (`ConicAlgebra.ext`, new in `Conic/Defs.lean`).
  The hypothesis is **discharged for separably closed fields**:
  `n(a·1 + u) = a² + t(u) a + n(u)`, so a root of `X² + t(u) X + n(u)` gives a null vector, nonzero
  as soon as `u ∉ K·1`. In characteristic ≠ 2 the discriminant is a square because `X² − c` is
  separable; in characteristic 2 the polynomial is separable exactly when `t(u) ≠ 0`, and such a
  `u` exists because the norm is regular (`GPR 19.11`) — otherwise `1` would lie in the kernel of
  the polar form. ⚠ Separable, not algebraic, closure is what the proof consumes, which is the
  point of `GPR 23.12`: over a separably closed field of characteristic 2 there are still
  inseparable quadratic algebras; they are conic algebras, but not composition algebras
  (`Composition/Inseparable.lean`).
- **The reals.** By Sylvester's law of inertia, exactly one composition **division** algebra in each
  dimension 1, 2, 4, 8 — namely `ℝ, ℂ, ℍ, 𝕆` — plus the split one in dimensions 2, 4, 8. **Proved**
  (`Composition/Fields/Real.lean`), on the quadratic-form input
  `QuadraticForm.equivalent_of_anisotropic_of_finrank_eq` (`QuadraticForm/Real.lean`): an
  anisotropic real form taking a positive value is a sum of squares, so anisotropic real forms
  taking positive values are classified by their dimension. The norm takes the value `1` at the
  identity element, hence is positive definite (`posDef_norm_of_hasTwoSidedInverses`), and Layer 9
  turns the isometry into an algebra isomorphism. `isomorphic_realTower_of_hasTwoSidedInverses` is
  the resulting list, and `isSplitOfRank_or_isomorphic_realTower` adds the split algebras. Each
  division statement in this and the next bullet is also stated with `IsDivision`
  (`isomorphic_realTower_of_isDivision`, `not_isDivision_of_finite`, …).
- **Finite fields.** By Chevalley–Warning every form in ≥ 3 variables is isotropic, so all
  quaternion and octonion algebras split; the only non-split composition algebra is `𝔽_{q²}` in
  dimension 2. **Proved** (`Composition/Fields/Finite.lean`, `QuadraticForm/FiniteField.lean`).
  `QuadraticForm.not_anisotropic_of_two_lt_finrank` feeds the `GPR 11.8` polynomial of the form —
  total degree 2, which is `QuadraticForm.totalDegree_toMvPolynomial_le`, new here — to mathlib's
  Chevalley–Warning; anisotropy would make the zero vector the only solution, contradicting
  divisibility of the solution count by the characteristic. Hence `isSplitOfRank_of_finite` in
  dimensions 4 and 8, `not_hasTwoSidedInverses_of_finite`, and uniqueness in every dimension other
  than 2 (`isomorphic_of_finite_of_ne_two`). In dimension 2, `GPR 19.8` makes the algebra
  associative and commutative; anisotropy makes it a field, and mathlib's
  `FiniteField.algEquivExtension` identifies any two such degree-two extensions, including in
  characteristic 2. Thus `isomorphic_of_finite_of_hasTwoSidedInverses_two` proves uniqueness of the
  dimension-two division algebra without redeveloping Artin–Schreier theory, and
  `exists_isComposition_hasTwoSidedInverses_not_isSplitOfRank_two` proves the matching existence:
  any quadratic field extension of `𝔽_q`, with the conic structure of `GPR 19.8`, is one.
- **Local fields** (complete discretely valued with finite residue field, e.g. `ℚ_p`). Every form
  in ≥ 5 variables is isotropic, so **every octonion algebra splits**; there is a **unique**
  quaternion division algebra; in characteristic ≠ 2 the dimension-2 algebras are parameterized by
  `K×/K×²`. **Not proved.** The composition-algebra half is available — feed
  "every 8-dimensional form over `K` is isotropic" to
  `IsComposition.isSplitOfRank_of_forall_not_anisotropic` — but the quadratic-form input, that the
  `u`-invariant of a local field is 4, is not in mathlib and is not attempted here. The same
  applies to the quaternion and dimension-2 clauses.
- **Fields with surjective quaternion reduced norms.** *If every quaternion `F`-algebra has
  surjective reduced norm, then every octonion `F`-algebra is split* — the octonion norm is a
  3-fold Pfister form doubling the quaternion 2-fold Pfister norm, so surjectivity forces isotropy.
  Instances: totally imaginary number fields and global fields with no real places (`GPR 23.21`,
  with `GPR 23.22` giving the Albert–Jacobson refinement); and `ℂ(x,y)`. The general mechanism is
  **proved** (`Composition/Fields/SurjectiveNorm.lean`):
  `isSplitOfRank_eight_of_forall_surjective_norm` writes the octonion algebra as `Cay(B, −n(v))`
  by `GPR 19.17` and turns a solution of `n_B(x) = −n(v)` into the nonzero null vector `x + v`.
  The instances are **not proved**: each rests on a substantial number-theoretic or
  function-field input, none of which is in mathlib, and the number-field case needs
  Hasse–Minkowski, which is out of scope.

**Out of scope:** anything requiring Hasse–Minkowski or Hilbert reciprocity, including the full
global/number-field classification (`GPR 23.16–23.20`).

---

## Design decisions

These are settled; changing them requires a good argument and a discussion, not a quiet edit.

1. **Exactly two named algebra notions: `ConicAlgebra` and `CompositionAlgebra`.** Everything
   between them is expressed as hypotheses, not as new types. In particular there is **no**
   `PreCompositionAlgebra`, even though GPR defines one: `GPR 19.7(a)` shows pre-composition
   algebras are not stable under base change (`GPR 19.4` is the counterexample), and base-change
   stability is the property we want our named notions to have. The one theorem that motivates the
   notion (`GPR 19.3`) is stated with explicit unbundled hypotheses instead.
2. **Three independent axes, never bundled.** Algebra structure (unital, alternative), norm
   regularity (nondegenerate, non-singular, regular), and module regularity (`Module.Finite`,
   `Module.Projective`, constant rank) are separate hypotheses. Every result carries exactly the
   hypotheses its proof consumes.
3. **Build GPR's regularity notions, named after their source.** `GPR 11.11` distinguishes weakly
   regular, non-degenerate, non-singular, and regular. Over a general ring these are not linearly
   ordered: regular ⇒ weakly regular ⇒ non-degenerate, and regular ⇒ non-singular for finitely
   generated projective modules, but nothing else (see `QuadraticForm/Regularity.lean` for
   separating examples). We reuse mathlib's `polarBilin.Nondegenerate` for weak regularity, and add
   `QuadraticForm.IsGPRNondegenerate`, `IsGPRNonsingular` (base-change stable, what composition
   algebras need), and `IsGPRRegular` for the other three. Because the literature disagrees on these
   words — `EKM` reuses "regular" and "non-degenerate" for a *different* two-rung ladder built from
   the same radical — every predicate is named after its source (`IsGPR…`, `IsEKM…`; see
   `QuadraticForm/Regularity.lean`), never left as a bare
   `IsNondegenerate`/`IsRegular`/`IsNonsingular`.
4. **Polar, never `associated`.** All norm/trace/conjugation API routes through the un-halved
   `QuadraticMap.polar` / `QuadraticForm.polarBilin`. `QuadraticMap.associated` is half the polar
   and requires `Invertible 2`; using it silently assumes `2 ∈ kˣ` and breaks every
   characteristic-2 example.
5. **`μ : k` arbitrary in Cayley–Dickson.** Unit hypotheses live on theorems, not on the
   construction.
6. **Recover mathlib's objects, don't duplicate them** — but asymmetrically, where the mathematics
   is asymmetric. See below.
7. **Work over `CommRing` by default; add an `IsLGRing k` hypothesis or `[Field K]` only where
   needed.** The objects are always general; only theorems carry the stronger hypotheses. This is
   what makes the field case a genuine instance of the LG case rather than a parallel development:
   `IsLGRing` is a predicate, so the field case is the LG theorem applied to `isLGRing_of_field K`.

---

## Boundaries and traps

Six places where the obvious thing is wrong. Each has bitten this development already.

**1. Regularity words are source-specific; name predicates after their source.** mathlib's
`LinearMap.BilinForm.Nondegenerate` means the map to the dual is *injective* (separating) — GPR
calls this "weakly regular". GPR's own "non-degenerate" means `Rad(q) = 0`
(`QuadraticForm.IsGPRNondegenerate`), GPR's "regular" means the map to the dual is an *isomorphism*
(`QuadraticForm.IsGPRRegular`), and GPR's "non-singular" is base-change-stable vanishing of the
radical (`QuadraticForm.IsGPRNonsingular`). For finite-dimensional forms over a field of
characteristic not `2` these all agree; in characteristic `2` they separate already over a field
(`x²` over `𝔽₂` is non-degenerate and non-singular but not weakly regular), and over rings they
diverge further (`x²` over `𝔽₂[ε]/(ε²)` is non-singular with `ε` in its radical). `EKM`
independently has its own two-rung ladder from the same radical, calling its rungs "regular" (=
GPR's non-degenerate) and "non-degenerate" (`QuadraticForm.IsEKMNondegenerate`, only meaningful over
a field, ≠ GPR's non-degenerate). Always say — and name — which source's sense you mean.

**2. mathlib's isotropy is *nonzero*; GPR's is *unimodular*.** `QuadraticMap.Anisotropic Q` means
`Q x = 0 → x = 0`, so its negation means a **nonzero** null vector. GPR (`11.17`) requires a
**unimodular** null vector. Over a field these coincide; over a ring unimodular is strictly
stronger. `GPR Exc. 12.38(c)` proves their equivalence only for free modules of finite rank over a
PID, and `GPR 22.19` lists them as separate conditions, (ii) and (iii), precisely because they are
separate. The reduced-algebra layer must use the GPR notion, which is named after its source
(`QuadraticMap.IsGPRIsotropic`), never left as a bare `IsIsotropic`.

**3. `QuaternionAlgebra` is a free rank-4 presentation, not "the rank-4 composition algebras".**
The two notions do not line up over a general base:
- *Too wide:* `QuaternionAlgebra k c₁ c₂ c₃` accepts arbitrary structure constants, so its norm
  need not be non-singular. Some `QuaternionAlgebra`s are not composition algebras.
- *Too narrow:* it is a **presentation** — a basis `1, i, j, k` with a fixed multiplication table
  — so it only ever produces free modules, whereas a composition algebra is only required to be
  projective of constant rank. Nothing in the definitions makes every rank-4 composition algebra a
  `QuaternionAlgebra`.

  ⚠ Keep two questions apart: whether the underlying module is free, and whether a presentation of
  this shape exists. Freeness is necessary for a presentation but is not the same statement, and in
  rank four it is often automatic. A rank-4 composition algebra is an Azumaya algebra, étale-locally
  `M₂`, and conjugation `x ↦ g x g⁻¹` on `Mₙ` has determinant `det(g)ⁿ det(g)⁻ⁿ = 1`, so its
  determinant module is trivial. Over a Dedekind domain a projective module of rank four with
  trivial determinant is free (Steinitz), so a nontrivial class group does **not** produce
  rank-4 composition algebras with non-free modules.

  The correct statements are two asymmetric lemmas: a `QuaternionAlgebra` with non-singular norm is
  a rank-4 composition algebra (any commutative ring); and every constant-rank-4 composition algebra
  is a `QuaternionAlgebra` **over an LG ring**, where `GPR 19.16` writes it as a Cayley–Dickson
  double of a quadratic étale algebra and constant-rank projectives are free. In general a rank-4
  composition algebra is an Azumaya algebra of rank 4 — a twisted form of `M₂(R)` — and only
  locally a `QuaternionAlgebra`.

  ⚠ None of this obstructs the **specific** identification `Cay₄ ℝ (-1) (-1) ≃ₐ[ℝ] ℍ[ℝ]`, which
  is proved in `Composition/ComplexQuaternion.lean`: over `ℝ` the module is free and the structure
  constants are the standard ones. What fails in general is the *uniform* statement, not this
  instance.

**4. The norm form does not determine the algebra over general rings.** Gille, *Octonion algebras
over rings are not determined by their norms*, Canad. Math. Bull. **57** (2014), no. 2, 303–309,
constructs octonion algebras over a ring with isometric norms that are not isomorphic. So the LG
hypothesis (`IsLGRing k`) in Layer 9 cannot be dropped. Do not record the general-ring statement as
an open problem: it is a known counterexample. The form-level shadow of the same obstruction is
`GN 6.5`'s remark that cancellation fails when the cancelled form is merely nonsingular.

**5. Witt cancellation's hypothesis asymmetry is load-bearing.** `q₁, q₂` nonsingular but `q₃`
**regular**. Weakening `q₃` to nonsingular makes the statement false — the counterexample is
Elman–Karpenko–Merkurjev, p. 49, cited at the end of `GN §6`.

**6. Alternativity does not make conjugation an anti-homomorphism over a ring.** The field proof
("if `x ∉ k·1` then `1, x` are independent") is a *field* proof, and the statement it proves is
false over a general base — even for **associative** algebras.
`Conic/TraceDefectCounterexample.lean` exhibits an associative conic algebra over `ℤ/4`, namely
`ℤ/4 · 1 ⊕ (ℤ/2)²` with a non-symmetric multiplication `β` on the second summand, for which
`conj(m₁m₂) = 2·1 ≠ 0 = conj(m₂)·conj(m₁)`; the whole thing is checked by `decide`. What survives
over any base is the identity `ȳ x̄ − conj(xy) = (t(x)t(y) − n(x,y) − t(xy))·1` and, for alternative
algebras, the fact that the obstruction times `x` is a multiple of `1`. Getting the
anti-homomorphism property over a ring needs the algebra to be projective, which is a hypothesis on
the *theorem*, not on `ConicAlgebra` (`ConicAlgebra.conj_mul_of_projective`).

This is a trap for the reader, not an error in the literature: `GPR` states the criterion as an
iff (`GPR 16.10(a)`), puts projectivity into the hypotheses of the theorems that deliver the
involution (`GPR 16.14(b)`, `GPR 17.6`), and warns against the false claim explicitly in
`GPR 17.4`. Our counterexample is a small variant of `GPR Exc. 17.8`, due to McCrimmon, which does
the same job over the dual numbers `k₀[ε]`.

---

## References

**Primary.**

- S. Garibaldi, H. P. Petersson, M. Racine, *Albert Algebras over Commutative Rings*, Cambridge
  University Press. Conic algebras (Ch. 16), Cayley–Dickson (Ch. 18), composition algebras
  (Ch. 19), regularity ladder (11.11), Zorn vector matrices (21.18), reduced algebras (Ch. 22),
  classification over special fields (Ch. 23).
- P. Gille, E. Neher, *Group schemes over LG-rings and applications to cancellation theorems and
  Azumaya algebras*, European Journal of Mathematics **11** (2025), article 42.
  [doi:10.1007/s40879-025-00825-w](https://doi.org/10.1007/s40879-025-00825-w). LG rings (§2),
  cancellation theorems (§6, with Witt cancellation of quadratic forms in 6.5), hermitian and
  quadratic forms over rings (Appendix C), and the algebraic-integers capstone (Example 3.15).
  ⚠ Cite the **published** numbering, not the arXiv preprint's — they differ (e.g. preprint 1.6 =
  published 2.6; preprint 5.5 = published 6.5; preprint 2.15 = published Example 3.15).

**Secondary.**

- R. D. Schafer, *An Introduction to Nonassociative Algebras*. Alternative algebras, Moufang,
  Artin's theorem.
- T. A. Springer, F. D. Veldkamp, *Octonions, Jordan Algebras and Exceptional Groups*.
- J. C. Baez, *The Octonions*, Bull. AMS **39** (2002).
- T. Y. Lam, *Introduction to Quadratic Forms over Fields*; R. Scharlau, *Quadratic and Hermitian
  Forms*; O. T. O'Meara, *Introduction to Quadratic Forms*.
- P. Gille, *Octonion algebras over rings are not determined by their norms*, Canad. Math. Bull.
  **57** (2014), 303–309. The counterexample bounding Layer 9.
- R. Baeza, *Quadratic Forms over Semilocal Rings*, Lecture Notes in Math. **655**, Springer 1978;
  I. Dias, *Formas Quadráticas Sobre LG-Anéis*, Ph.D. thesis, Universidade Estadual de Campinas,
  1988 (II.6.4 is Witt cancellation for regular forms over LG rings); M. Knebusch. The elementary
  route to Witt cancellation.
- R. Elman, N. Karpenko, A. Merkurjev, *The Algebraic and Geometric Theory of Quadratic Forms*,
  AMS Colloq. Publ. **56**, 2008. Witt cancellation over arbitrary fields (Thm. 8.4); the p. 49
  counterexample showing cancellation fails for merely nonsingular forms.
- M. Auslander, O. Goldman, *The Brauer group of a commutative ring*; M.-A. Knus, M. Ojanguren,
  *Théorie de la descente et algèbres d'Azumaya*. The Azumaya picture behind trap 3.
- D. Estes, R. Guralnick; B. McDonald, W. Waterhouse. Origins of LG rings.

---

## Status

The library **builds clean**: no `sorry` anywhere, and no axioms beyond Lean's own `propext`,
`Quot.sound` and `Classical.choice`. Every result the layers above describe as proved is proved. The
layer descriptions also mark what is *not* formalized; besides the Layer 11 boundaries below, that
is notably the LG property of `ℤ̄` (`GN 2.2(e)`), closure of LG rings under integral extensions
(`GN 2.2(b)`), and the trilinear associator and nuclei as sub-structures (Layer 1).

A handful of results at the edges of Layer 11 are deliberately **not** formalized, because they
need inputs mathlib does not yet have — Hasse–Minkowski, the `u`-invariant of a local field, the
symplectic-basis theorem for alternating forms. Those boundaries are recorded explicitly rather
than papered over.

**[`RESULTS.md`](RESULTS.md) is the detailed record**: every result, indexed by its citation in
`GPR`, `GN`, `EKM` and `Dias`, with the Lean names that prove it, the route the proof takes where
it departs from the literature, and what is out of scope and why.

---

## Building

```
lake exe cache get   # fetch mathlib oleans
lake build
```

The mathlib revision is pinned in `lake-manifest.json`. See [`AGENTS.md`](AGENTS.md) for the
policy on updating it.

## License

Apache 2.0, matching mathlib.
