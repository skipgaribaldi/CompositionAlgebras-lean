# AGENTS.md — how to write Lean in this repository

Instructions for AI agents and human contributors. This document is about **how** to write the
code; [`README.md`](README.md) is about **what** the code says mathematically, and
[`RESULTS.md`](RESULTS.md) records result by result what is proved. Read the README first — in
particular its *Design decisions* and *Boundaries and traps* sections, which are mathematical
commitments this document assumes you have absorbed.

---

## Current task

The library is complete in the sense that it builds with no `sorry` and no custom axioms. The
work now is maintenance and improvement: keeping up with mathlib releases, golfing proofs,
tightening hypotheses, and upstreaming what mathlib will take.

Follow the [mathlib style guide](https://leanprover-community.github.io/contribute/style.html)
without local variation. The rest of this document is the house guidance that sits on top of it.

Agents: this repository has a Lean 4 skill installed. Use it.

---

## 0. The one rule that matters most

**mathlib is canonical. This repository is not standalone.**

We depend on mathlib and treat it the way the
[Tau Ceti](https://github.com/TauCetiProject/TauCeti) project does: as the library that defines
the conventions, owns the general-purpose material, and settles design questions. Our job is to
supply what mathlib is missing for composition algebras and Witt cancellation — nothing more.

Before you define anything, **search mathlib for it**. If it exists, import it and use it. If
something close exists but not quite right, prefer adapting your statement to mathlib's notion
over introducing a competing one; if you genuinely must diverge, document the divergence
explicitly with a `⚠` docstring paragraph explaining what mathlib's notion is, what ours is, and
where they agree (see §6).

Reinventing a mathlib definition is the most costly error you can make here, because it silently
forks the API and makes every downstream lemma unusable by anyone else.

### Things that are already in mathlib — use them

- `NonUnitalNonAssocRing`, `NonAssocRing`, `NonUnitalNonAssocSemiring`,
  `NonUnitalNonAssocAlgebra`, `NonUnitalAlgHom`, `AlgEquiv`, `MulOpposite`
- `QuadraticMap`, `QuadraticForm`, `QuadraticMap.polar`, `QuadraticForm.polarBilin`,
  `QuadraticMap.Anisotropic`, `QuadraticMap.IsometryEquiv`, `QuadraticForm.baseChange`,
  `QuadraticForm.prod`, `QuadraticForm.dualProd` (the hyperbolic form)
- `LinearMap.BilinForm`, `.Nondegenerate`, `.SeparatingLeft`, `.IsSymm`
- `Module.Free`, `Module.Finite`, `Module.Projective`, `Module.rank`, `Module.finrank`, `Basis`,
  `Module.Dual`, `Module.IsUnimodular`, `Submodule`, `Algebra.TensorProduct`
- `Complex`, `Quaternion`, `QuaternionAlgebra`, `Analysis.Quaternion`
- `FieldTheory.ChevalleyWarning`, `LinearAlgebra.QuadraticForm.Real`, `Padics`
- `Polynomial`, `MvPolynomial`, `Ideal`, `IsLocalRing`, `Jacobson` radical API

If you find yourself writing `def polar'` or `structure MyQuadraticForm`, stop.

---

## 1. Style: follow mathlib's, exactly

We use the [mathlib style guide](https://leanprover-community.github.io/contribute/style.html)
and [naming convention](https://leanprover-community.github.io/contribute/naming.html) without
local variation. Highlights, since they are the ones most often violated:

- **100 character line limit.** Hard.
- **Two-space indentation.** No tabs.
- Theorem names are `snake_case` descriptions of the statement in terms of the symbols appearing
  in it, reading left to right: `norm_mul`, `associator_swap`, `isLGRing_of_isLocalRing`.
- Types and structures are `UpperCamelCase`; terms and proofs are `lowerCamelCase` or
  `snake_case` per the mathlib rules (`def`s producing data: `lowerCamelCase`; `theorem`/`lemma`:
  `snake_case`).
- Predicates on structures are `Is…` or `…Class` mixins: `IsAlternative`, `IsLGRing`,
  `IsComposition`.
- `variable` lines at the top of sections; do not repeat hypotheses in every declaration.
- Prefer `theorem` over `lemma` for results intended to be used elsewhere; both are fine.
- Anonymous constructor notation `⟨_, _⟩`, `fun` over `λ`, `·` for placeholders.

Run `lake lint` (not `lake exe lint`) and `lake exe lint-style CompositionAlgebras` before
considering a file done. The second is mathlib's text linter; among other things it rejects
characters outside mathlib's unicode allowlist, so docstrings write the conjugate of `x` as
`conj x` (`(conj x)` when it is a factor in a product), never `x̄` with a combining macron, and use
`↔`/`⇐` rather than `⟺`/`⟸`.

---

## 2. Hypotheses: unbundled, minimal, honest

This is the central discipline of the repository and the thing most likely to be got wrong.

**State every result with exactly the hypotheses its proof consumes.** Not more, not fewer, and
not a convenient bundle.

Three independent axes recur throughout; keep them separate:

| Axis | Typical hypotheses |
|---|---|
| Algebra structure | `[NonAssocRing A] [Module k A] [SMulCommClass k A A] [IsScalarTower k A A]`, `[IsAlternative A]` |
| Norm regularity | `(Q.polarBilin).Nondegenerate`, `Q.IsGPRNonsingular`, `Q.IsGPRRegular` |
| Module regularity | `[Module.Finite k A]`, `[Module.Projective k A]`, constant rank |

Consequences:

- Do **not** fold projectivity or nondegeneracy into `ConicAlgebra`. The sedenions must be conic
  without either; Cayley–Dickson and the conjugation calculus use neither.
- Do **not** create a `PreCompositionAlgebra` structure to package "projective + GPR-nondegenerate +
  multiplicative". State `GPR 19.3` with those three as separate hypotheses. (Reason: `GPR 19.7(a)`
  — the bundle is not base-change stable.)
- Do **not** write `[Field K]` when the proof only needs an LG hypothesis `(hLG : IsLGRing k)`, and
  do not assume `IsLGRing k` when the proof works over any `CommRing`.
- Do **not** write `[IsLocalRing k]` as a stand-in for `IsLGRing k`. We have `IsLGRing`; use it.

**The default base is `variable (k : Type*) [CommRing k]`.** Objects are always defined over a
general commutative ring. Stronger hypotheses attach to *theorems*, never to *definitions*. This
is what makes the field case a genuine instance of the LG case rather than a duplicate
development. `IsLGRing` is a plain predicate (`def IsLGRing (R) : Prop`), not a class: LG theorems
take an explicit hypothesis `(hLG : IsLGRing k)`, and the field case is obtained by passing
`isLGRing_of_field K`.

---

## 3. File and directory organization

```
CompositionAlgebras/
  Module/                -- layer 0: plain commutative algebra, mathlib-only imports
    IdempotentDecomposition.lean
                         -- M ≃ ∏ M ⧸ (1-eᵢ)M for complete orthogonal idempotents
    RankDecomposition.lean
                         -- GPR Exc. 9.31; rankIdempotent, and what the rank-zero one does;
                         -- constant rank is stable under base change and locally free
    IdempotentFactor.lean
                         -- modules over an idempotent factor k ⧸ (1 - e); freeness of
                         -- constant-rank projectives passes to the factors (GPR 22.16)
    SelfAnnihilating.lean
                         -- φ x • x = 0 on a f.g. projective module forces φ = 0
    Unimodular.lean      -- API for mathlib's Module.IsUnimodular: GPR 9.13's form, the field
                         -- case, the splitting M ≃ R × ker l. Lives here, not in
                         -- QuadraticForm/, because no quadratic form is involved and LGRing/
                         -- needs it
    Invertible.lean      -- invertible modules and line bundles
    ExteriorPower.lean   -- exterior powers of finite projective modules
    AlternatingBaseChange.lean
                         -- base change of alternating trilinear forms
    VectorProduct.lean   -- vector product pairs (GPR 22.14)
  Nonassociative/        -- layer 0: alternative algebras know nothing about norms
    Associator.lean      -- associator API, nucleus (the center is mathlib's)
    Subalgebra.lean      -- unital subalgebras of non-associative algebras
    Division.lean        -- IsDivision: division algebras in the sense of GPR 8.6
    Alternative/
      Defs.lean          -- IsAlternative, associator alternation
      Moufang.lean       -- the Moufang identities
      Artin.lean         -- Artin's theorem
      PowerAssociative.lean
                         -- power-associativity of alternative rings
      Peirce.lean        -- Peirce projections in alternative algebras
  LGRing/                -- layer 1: may import Module/
    Defs.lean            -- IsLGRing, equivalent formulations; aeval along a commuting square
    ValueIdeal.lean      -- the ideal generated by the values of p; the finitary criterion
                         -- "valueIdeal = ⊤ ⇒ represents a unit", used by every example below
    Examples.lean        -- zero ring, fields, semilocal, algebraic integers
    NonExamples.lean     -- ℤ, R[t]
    Semilocal.lean       -- semilocal rings are LG-rings
    Jacobson.lean        -- R LG ↔ R ⧸ Jac(R) LG (GPR 11.21(i))
    Products.lean        -- finite products of LG-rings (GPR 11.21(ii)); arbitrary products of
                         -- fields, in particular F^I
    DirectLimit.lean     -- directed unions and direct limits of LG-rings (GN 2.2)
    ZeroDimensional.lean -- von Neumann regular and Krull-dimension-zero rings are LG (GN 2.2),
                         -- by gluing witnesses over a partition into idempotent blocks
    ConstantRank.lean    -- constant-rank projective ⇒ free (GN 2.6(b), GPR 11.24)
    Unimodular.lean      -- faithfully projective modules contain a unimodular element (GN 2.6(a))
  QuadraticForm/         -- layer 2: may import Module/, LGRing/
    Regularity.lean      -- IsGPRNonsingular, IsGPRRegular, IsEKMNondegenerate; relation to
                         -- mathlib Nondegenerate
    BaseChangeProjective.lean
                         -- base change of quadratic maps along R → A, without inverting 2
    OrthogonalComplement.lean
                         -- a submodule with regular restricted form splits off orthogonally
    Isotropic.lean       -- GPR-sense isotropy (unimodular null vector)
    NonsingularOverFields.lean
                         -- EKM Lemma 7.16 and GPR Exc. 11.37 over a field
    Polynomial.lean      -- a quadratic form on a free module as a polynomial (GPR 11.8)
    Representation.lean  -- the representation lemma (GPR 11.26, GN Lemma C.13(a))
    FiniteField.lean     -- Chevalley-Warning: forms in >= 3 variables over a finite field are
                         -- isotropic
    Real.lean            -- anisotropic real forms are definite, hence classified by dimension
                         -- and sign
    Hyperbolic.lean      -- regularity of mathlib's hyperbolic form QuadraticForm.dualProd;
                         -- q ⊥ -q ≅ dualProd for q regular
    HyperbolicPair.lean  -- hyperbolic pairs, Siegel-Eichler transvections, dilations
    PlaneSplitting.lean  -- a hyperbolic pair splits off a hyperbolic plane
    PlaneCancellation.lean
                         -- transitivity on pairs ⇒ cancellation of a plane
    PlaneTransitivity.lean
                         -- Dias II.6.1-II.6.2: transitivity on hyperbolic pairs (the LG step)
    Cancellation.lean    -- reduction of Witt cancellation to the hyperbolic case
    WittCancellation.lean
                         -- Witt cancellation itself (GN 6.5)
  Conic/                 -- layer 3: may import Module/, Nonassociative/, QuadraticForm/
    Defs.lean            -- ConicAlgebra (GPR 16.1)
    Basic.lean           -- trace, conjugation, core identities
    BaseChange.lean      -- S ⊗[k] A as a conic algebra, for A f.g. projective (GPR 16.3)
    BaseChangeMultiplicative.lean
                         -- base change preserves IsMultiplicative
    Projective.lean      -- 1 unimodular; the trace defect vanishes (GPR 16.7, 16.14(b))
    TraceDefectCounterexample.lean
                         -- an associative conic algebra over ℤ/4 whose conjugation is not an
                         -- anti-homomorphism (README trap 6)
    Multiplicative.lean  -- IsMultiplicative (GPR 19.1); norm-associativity (GPR 16.5)
    Division.lean        -- division, two-sided inverses, anisotropy; GPR 13.8 for alternative
                         -- conic algebras over a field
    Subalgebra.lean      -- the conic structure restricted to a unital subalgebra
    Doubling.lean        -- GPR 18.1: B + Bv inside an ambient algebra, for v orthogonal to B
    Kirmse.lean          -- Kirmse's identities; alternativity under weak regularity
    Recognition.lean     -- GPR 19.3: a non-degenerate multiplicative form makes a unital
                         -- algebra conic alternative; the polar radical is central
    QuadraticAlgebra.lean
                         -- GPR 16.4: a unital projective algebra of rank two is conic
    CayleyDickson.lean   -- Cay(B, μ) (GPR 18.3, 18.4, 18.11)
    CayleyDicksonAssociative.lean
                         -- B commutative associative ⇒ Cay(B, μ) associative (GPR 18.14(b)),
                         -- with the Ring/Algebra structures that let the tower iterate
    CayleyDicksonAlternative.lean
                         -- B associative ⇒ Cay(B, μ) alternative (GPR 18.14(c))
    CayleyDicksonMultiplicative.lean
                         -- B associative multiplicative ⇒ Cay(B, μ) multiplicative (GPR Exc. 18.18)
    CayleyDicksonConverse.lean
                         -- the converse halves of GPR 18.14 and GPR 18.15
  Composition/           -- layer 4: may import anything
    Defs.lean            -- IsComposition (GPR 19.5)
    Basic.lean           -- alternativity (GPR 19.3), recognition
    Alternative.lean     -- composition algebras are alternative over an arbitrary base
    BaseChange.lean      -- S ⊗[k] A is a composition algebra (GPR 19.7)
    CayleyDickson.lean   -- Cay(B, μ) is a composition algebra (GPR 19.14, direction ⇐)
    CayleyDicksonIff.lean
                         -- GPR 19.14 in full: Cay(B, μ) is composition iff B is regular
                         -- associative composition and μ a unit; the double is regular
    Doubling.lean        -- GPR 19.16(a): a regular subalgebra splits off, over an LG ring
    QuadraticSubalgebra.lean
                         -- quadratic subalgebras generated by one element (GPR 19.8); over an
                         -- LG ring, constant rank two means monogenic
    RankTwoSubalgebra.lean
                         -- over a field, rank > 1 gives a separable quadratic subalgebra
                         -- (the field case of GPR 19.16(b))
    RankDichotomy.lean   -- the regular-or-rank-one dichotomy
    RankOneTwoFourEight.lean
                         -- the rank is 1, 2, 4 or 8 (GPR 19.18)
    Tower.lean           -- the Cayley-Dickson tower exhausts a composition algebra (GPR 19.17)
    ComplexQuaternion.lean
                         -- the first two rungs are mathlib's ℂ and ℍ
    Octonion.lean        -- the Cayley-Dickson tower Cay₂/Cay₄/Cay₈ over any base; octonions
    Examples.lean        -- ℝ, ℂ, ℍ, 𝕆: positive definiteness, division, where the tower breaks
    Sedenion.lean        -- conic, not composition (GPR 19.23); inverses without division
                         -- (GPR Exc. 19.29(e))
    Inseparable.lean     -- anisotropic conic algebras with vanishing polar form (GPR 19.4)
    InseparableAnisotropic.lean
                         -- an anisotropic witness for GPR 19.4
    NormClassification.lean
                         -- GPR 23.2-23.5: norm equivalences and the norm classification
    NormEquivalence.lean -- GPR 23.4: automorphisms are the unital norm equivalences; (b) for
                         -- quadratic algebras over any commutative ring, by localization
    QuadraticEtale.lean  -- GPR 19.8 standalone: a quadratic algebra is a conic algebra, and a
                         -- composition algebra exactly when etale
    Reduced/
      Defs.lean          -- elementary idempotents and reduced composition algebras (GPR 22.6-22.9)
      Peirce.lean        -- Peirce decomposition at an elementary idempotent
      Reducedness.lean   -- reduced composition algebras (GPR 22.6-22.7)
      Hyperbolic.lean    -- the norm of a reduced composition algebra is hyperbolic (GPR 22.9(iv))
      Zorn.lean          -- Zorn vector matrices (GPR 21.18)
      Split.lean         -- the split composition algebras (GPR 21.19)
      Splitness.lean     -- split composition algebras (GPR 21.19)
      RankTwo.lean       -- reduced algebras of rank two are split (GPR 22.10)
      TwistedMatrix.lean -- L-twisted 2-by-2 matrices (GPR 22.12, 22.13)
      Orientation.lean   -- oriented rank-three projective modules (GPR 22.14); every
                         -- vector-product pair comes from a unique orientation
      TwistedZorn.lean   -- twisted Zorn vector matrices (GPR 22.14)
      RankEight.lean     -- reduced composition algebras of rank eight (GPR 22.15)
      OrientedRankEight.lean
                         -- GPR 22.15 with an orientation: reduced octonion algebras are the
                         -- twisted Zorn algebras Zor(M, θ)
      Classification.lean
                         -- reduced composition algebras over LG rings (GPR 22.16)
      Capstone.lean      -- splitting octonion algebras from their quadratic etale subalgebras
    Fields/
      Basic.lean         -- the two mechanism theorems over a field: split = isotropic, and the
                         -- norm as a complete invariant
      FractionField.lean -- GPR 22.19(i): splitness over the fraction field of a PID
      SepClosed.lean     -- fields over which every quadratic etale algebra splits (GPR 23.12)
      Real.lean          -- GPR 23.13: R, C, H, O
      Finite.lean        -- GPR 23.14, via Chevalley-Warning
      SurjectiveNorm.lean
                         -- GPR 23.21: surjective quaternion norms split the octonions
```

Adjust as the development dictates, but respect the shape: **one mathematical idea per file**,
directories mirroring the layers in the README.

### Import discipline (this is not optional)

Several parts of this repository are plausible mathlib contributions and must stay liftable. The
rule that preserves this:

> **General-purpose files must not import composition-algebra-specific files.**

Concretely, the directories form five layers, and a file may import mathlib plus any directory in
a **strictly lower** layer (plus its own):

| Layer | Directory | May import |
|---|---|---|
| 0 | `Module/` | mathlib only. Plain commutative algebra; no forms, no algebras. |
| 0 | `Nonassociative/` | mathlib only. Alternative algebras know nothing about norms. |
| 1 | `LGRing/` | `Module/` |
| 2 | `QuadraticForm/` | `Module/`, `LGRing/` |
| 3 | `Conic/` | `Module/`, `Nonassociative/`, `QuadraticForm/` |
| 4 | `Composition/` | anything |

`Module/` and `Nonassociative/` are independent of each other; nothing imports `Composition/`.
**This layering is acyclic and must stay so** — a cycle between two directories means a definition
is in the wrong place, not that the rule needs relaxing.

If you find yourself wanting to import "upwards", the definition is in the wrong file. Move it,
don't add the import. (`Module/Unimodular.lean` lives in `Module/` and not in `QuadraticForm/`
for exactly this reason: `LGRing/` needs its unimodular-element API, and that API is module
theory with no quadratic form in sight.)

Keep imports minimal in general: import the specific mathlib files you need, not
`import Mathlib`. (`import Mathlib` is acceptable only in scratch files that are not part of the
build.)

### The module system

Every file is a Lean **module**, as in mathlib: the copyright header, then `module`, then the
imports as `public import …`, then the module docstring, then `@[expose] public section`.
Under the module system a file sees only what its imports export, so a declaration that a
mathlib file imports privately must be imported directly; and a `private` declaration may be used
in proofs but not in a public statement or in the body of an exposed (public) definition —
including the proof fields of a structure or instance. Make such a helper public, with a
docstring, rather than working around the check.

---

## 4. Documentation

Every file begins with a module docstring:

```lean
/-!
# Conic algebras

Defines conic algebras over a commutative ring, following [GPR, 16.1]: a unital,
not-necessarily-associative algebra with a chosen quadratic norm satisfying `n 1 = 1` and the
degree-2 identity.

## Main definitions

* `ConicAlgebra k A` : ...
* `ConicAlgebra.trace`, `ConicAlgebra.conj` : ...

## Main results

* `ConicAlgebra.conj_conj` : conjugation is an involution.
* `ConicAlgebra.mul_conj` : `x * conj x = n x • 1`.

## Implementation notes

The norm is bundled as data, not as an existential: over a general ring a conic algebra's norm
need not be unique [GPR, 16.1]. Trace and conjugation are derived from the *un-halved* polar
form `QuadraticMap.polar`; see the warning below about `QuadraticMap.associated`.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 16.1–16.16.
-/
```

In the references section, each reference gets its own line.

**Every definition and every non-obvious theorem gets a docstring**, and every statement drawn
from the literature cites its source by number: `[GPR, 19.5]`, `[GN, 5.5]`. A reader must be able
to check our formalization against the book without guessing which result we mean.

Where our convention diverges from mathlib's or from a naive reading, add a `⚠` paragraph
explaining the divergence. See §6 for the mandatory ones.

---

## 5. `sorry` policy

- `sorry` is permitted while a layer is under construction, but every `sorry` must be accompanied
  by a comment saying what is missing and, where relevant, which reference result would supply it.
- A file with `sorry` in it must say so in its module docstring.
- `sorry` in a **definition** (as opposed to a proof) is a design smell: it usually means the
  statement is not yet properly specified. Prefer to leave the definition out entirely, or to
  write the specification as a comment, over committing a `sorry`-shaped definition that others
  will build on.
- Never use `sorry` to paper over a hypothesis you could not discharge. If a proof needs a
  hypothesis, add the hypothesis and note it — a theorem with honest hypotheses beats a false
  theorem with a `sorry`.
- Do not commit `sorry`-free-looking proofs that rely on `native_decide`, unsound axioms, or
  `Classical` hacks not used in mathlib. Check `#print axioms` on headline results.

---

## 6. Mandatory warnings to preserve

These five traps have already caused errors in the design of this development. Each must be
documented at the point of definition, and none may be silently "simplified away".

**(a) Polar, never `associated`.** All norm/trace/conjugation API routes through
`QuadraticMap.polar` / `QuadraticForm.polarBilin` — the un-halved `Q(x+y) − Q x − Q y`.
`QuadraticMap.associated` is half the polar and carries an `Invertible 2` hypothesis. Using it
silently assumes `2 ∈ kˣ` and makes the characteristic-2 examples unstatable. If you see
`Invertible 2` appearing in a conic-algebra file, something has gone wrong.

**(b) Regularity words are source-specific; name predicates after their source.** There is no
agreement across the literature on what "non-degenerate", "regular", or "non-singular" mean, and
worse, the *same* word means different things in different sources.
`LinearMap.BilinForm.Nondegenerate` (mathlib) is injectivity into the dual, not surjectivity —
GPR calls this "weakly regular". GPR's own "non-degenerate" is `Rad(q) = 0`
(`QuadraticForm.IsGPRNondegenerate`) and GPR's "regular" is the iso-to-dual condition
(`QuadraticForm.IsGPRRegular`); GPR's "non-singular" is base-change-stable vanishing of the
radical (`QuadraticForm.IsGPRNonsingular`). `EKM` independently has its own two-rung ladder
built from the same radical, calling its rungs "regular" (= GPR's non-degenerate) and
"non-degenerate" (`QuadraticForm.IsEKMNondegenerate`, ≠ GPR's non-degenerate, only meaningful over a
field) — see `QuadraticForm/Regularity.lean`'s module docstring for the full map. Never introduce a
bare `IsNondegenerate`/`IsRegular`/`IsNonsingular`; every regularity predicate must carry its
source's name (`IsGPR…`, `IsEKM…`), and every docstring that mentions regularity must state which
source's sense is meant.

**(c) GPR isotropy is *unimodular*, mathlib's is *nonzero*.** Do not implement GPR's isotropy as
`¬ QuadraticMap.Anisotropic`. Use mathlib's `Module.IsUnimodular` predicate. They agree over fields
and, for finitely generated projective modules, over PIDs (`GPR Exc. 12.38(c)`), and differ in
general. As with the regularity words in (b), the predicate carries its source's name:
`QuadraticMap.IsGPRIsotropic`, never a bare `IsIsotropic`.

**(d) The Cayley–Dickson scalar is arbitrary.** `Cay(B, μ)` takes `μ : k`, **not** `μ : kˣ`. Unit
hypotheses go on theorems. Encoding `μ : kˣ` in the construction breaks the sedenion example.

**(e) Conjugation is an anti-homomorphism only with a module hypothesis.** `conj (xy) = ȳ x̄` is
*not* a consequence of alternativity over a general base: `Conic/TraceDefectCounterexample.lean`
gives an associative conic algebra over `ℤ/4` where it fails (a small variant of `GPR Exc. 17.8`,
due to McCrimmon). Over a field it holds (`ConicAlgebra.conj_mul`); over a ring it needs the
algebra projective (`GPR 16.14(b)`, `GPR 17.6`), and the exact criterion is `GPR 16.10(a)`. When a
proof from the literature says "clearly `t(xy) = t(x)t(y) - n(x,y)`", check whether it is really a
field argument in disguise, and state the hypothesis the proof consumes
(`AGENTS.md` §2) rather than assuming the field case generalizes. Note that `GPR` itself does not
make this mistake — `GPR 17.4` warns against it explicitly — so when a claim here looks like it
contradicts the source, suspect the paraphrase before the source.

---

## 7. Proving: tactics and structure

- Prefer structured, readable proofs to long tactic soups. `calc` blocks for chains of equalities;
  `obtain`/`rcases` for destructuring; named `have`s for reusable intermediate steps.
- `simp` should be used with a specific simp set where the default is unpredictable. Do not commit
  proofs that depend on `simp` closing a goal by accident; if `simp` is doing real work, consider
  `simp only [...]` with the lemmas named.
- Mark genuinely simp-normal-form lemmas `@[simp]`, but sparingly — a bad `@[simp]` lemma in a
  non-associative setting can loop or normalize in the wrong direction.
- The associator/Moufang identities are the natural rewrite engine for alternative algebras;
  expose them as clean equational lemmas so downstream proofs can `rw` with them.
- When a proof is the same over fields and over LG rings — which is the common case here — write
  it **once**, with a hypothesis `(hLG : IsLGRing k)`, and get the field case by passing
  `isLGRing_of_field K`.
  Do not copy a field proof and generalize it later; that produces two proofs to maintain.

---

## 8. Working with the literature

- GPR and GN are the sources of record. When formalizing a numbered result, state it as closely to
  the source as the type theory permits, and note in the docstring any deliberate divergence
  (e.g. we state the `GN Example 3.15` capstone with "every quadratic étale algebra splits" rather
  than "simply connected", because that is what the proof consumes).
- ⚠ **Cite GN by its published numbering**, i.e. European Journal of Mathematics **11** (2025),
  article 42 — *not* the arXiv preprint's. The two differ throughout: preprint §1 = published §2,
  preprint 1.6 = published **2.6**, preprint 5.5 = published **6.5**, preprint 2.15 = published
  **Example 3.15**, and the cancellation section moved from §5 to §6. A docstring citing preprint
  numbers is a defect; fix it rather than adding a parenthetical.
- ⚠ **GPR is the opposite case: do not generalize the GN warning to it.** The pre-publication
  GPR extract uses the *same* numbering as the published Cambridge edition throughout, so a
  result number read off the extract may be cited directly with no cross-check.
  Note in particular that `GPR 18.15` is the corollary making the conjugation hypothesis of
  `GPR 18.14` automatic over a projective module; the criterion for the norm of a Cayley–Dickson
  double to permit composition is **`GPR Exc. 18.18`**.
- Where the literature has two versions of a result with different hypotheses (`GPR 11.27` vs.
  `GN 6.5` for Witt cancellation), target the stronger one but record that the weaker one is an
  acceptable milestone.
- Where a result is **false** in greater generality, say so in the docstring and cite the
  counterexample (Gille 2014 for the norm classification; EKM p. 49 for Witt cancellation with all
  forms merely nonsingular). Do not leave a false generalization looking like an open TODO.
- **Cite the original source alongside the textbook** wherever the repo's proof follows the
  original — e.g. Estes–Guralnick and McDonald–Waterhouse next to `GPR 11.24`.
- Do not import a proof strategy that drags in disproportionate machinery. Specifically: `GN 6.5`
  is proved via the cohomological Cancellation Principle `GN 6.1`, reductive group schemes over
  LG rings, and `SO(q)`-torsors — an enormous dependency. We want the elementary Dias/Baeza/
  Knebusch chain-equivalence route instead. Likewise, only the final paragraph of `GN Example 3.15`
  is in scope for the octonion capstone; its other proofs (Rumely's theorem, strong approximation,
  splitness of semisimple group schemes over `ℤ̄`) are not.

---

## 9. Build and dependencies

- mathlib is pinned in `lake-manifest.json`. Do not bump it casually; a bump is its own commit,
  with the build verified.
- `lake exe cache get` before `lake build`.
- New files must be added to the root import file (`CompositionAlgebras.lean`) so that
  `lake build` covers them, and must be modules (§3, *The module system*).
- The build must be warning-free, and `lake lint` must pass.
- CI must be green before merge. A red build is never "fixed later".

---

## 10. Checklist before submitting a change

- [ ] Searched mathlib for every notion introduced; nothing reinvented.
- [ ] Hypotheses are exactly those the proof consumes; nothing bundled.
- [ ] Objects defined over `CommRing`; `IsLGRing k` / `[Field K]` hypotheses only on theorems.
- [ ] Import discipline respected (no downward imports; general-purpose files mathlib-only).
- [ ] Module docstring with main definitions, main results, references.
- [ ] Every literature result cites its number.
- [ ] The four mandatory warnings (§6) preserved where relevant.
- [ ] Any `sorry` documented and flagged in the module docstring.
- [ ] Style: 100 columns, two-space indent, mathlib naming.
- [ ] `lake build` succeeds with no warnings; `lake lint` and `lake exe lint-style` pass.

---

## 11. Division of labour between the documents

Three documents, three jobs. Do not let them drift into copies of one another.

| File | Answers | Audience |
|---|---|---|
| `AGENTS.md` | How do I write Lean here? | contributors |
| `README.md` | What is the plan, and how does it map onto the Lean? | contributors |
| `RESULTS.md` | Which results are proved, and by which Lean names? | contributors |

- `README.md` is the **narrative account**: the layer structure, the mathematical conventions
  (*Design decisions*, *Boundaries and traps*), and how the Lean is organized. Per-result status
  belongs in `RESULTS.md`, not here.
- `RESULTS.md` is the **record of what is proved**, one row per citation in `GPR`, `GN`, `EKM`
  or `Dias`, naming the Lean declarations and saying where the proof departs from the literature.
  Rows must stay on a single line — GitHub's markdown does not render a table row that wraps.
- `AGENTS.md` is **how the Lean is written**: style, hypothesis discipline, file organization,
  and the traps recorded in §6. It carries no mathematical status of its own.
