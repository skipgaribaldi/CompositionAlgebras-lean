/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Prod
import Mathlib.LinearAlgebra.QuadraticForm.Radical
import Mathlib.LinearAlgebra.Dual.BaseChange
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Ideal.Nonunits
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.LocalProperties.Exactness
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.LinearAlgebra.TensorProduct.Tower
import CompositionAlgebras.QuadraticForm.BaseChangeProjective

/-!
# Regularity of quadratic forms: the radical, `IsGPRNondegenerate`, `IsGPRRegular`,
# `IsGPRNonsingular`, `IsEKMNondegenerate`

There is no agreement in the literature on the right words (nonsingular, regular, non-degenerate,
etc.) for regularity conditions on quadratic forms, and worse, the *same* word means different
things in different sources. To keep this straight, every regularity predicate in this file is
named after the source whose convention it follows.

`GPR 11.11` distinguishes four notions: **weakly regular** (the polar form is injective — mathlib's
`polarBilin.Nondegenerate`/`SeparatingLeft`, `AGENTS.md` §6(b)), **non-degenerate**
(`radical Q = ⊥`, `GN C.8(d)`), **non-singular** (the radical vanishes after every field base
change, `GN C.8(e)`), and **regular** (the polar form is an isomorphism onto the dual, not just
injective).

⚠ **Over a general ring these do not form a linear ladder.** Since `radical Q` lies in the kernel
of the polar form, regular ⇒ weakly regular ⇒ non-degenerate; and regular ⇒ non-singular for `M`
finitely generated projective (`GN (C.8.1)`). Nothing else holds in general. `x²` over `𝔽₂` is
non-degenerate (indeed non-singular) but not weakly regular, its polar form being zero; `x²` over
`𝔽₂[ε]/(ε²)` is non-singular but has `ε` in its radical; and `2x²` over `ℤ` is weakly regular but
not non-singular, since it vanishes modulo `2`. Over any field non-singular ⇒ non-degenerate (the
converse fails for `x² + t y²` over `𝔽₂(t)`, which acquires a radical vector over `𝔽₂(√t)`), and
for finite-dimensional forms over a field of characteristic not `2` all four notions agree.

`EKM` independently has its own two-rung ladder built from the same radical, calling its rungs
"regular" and "non-degenerate" — words that collide with, but do not mean the same thing as, GPR's
"regular" and "non-degenerate".

## Main definitions

* `QuadraticForm.IsGPRNondegenerate` : `QuadraticMap.radical Q = ⊥`, GPR's own "non-degenerate"
  rung. The radical is **mathlib's** `QuadraticMap.radical`, the submodule of vectors on which
  both `Q` and its polar form vanish (`GN C.8(d)`, `EKM` II §7). It lies in the kernel of the polar
  form, so `radical Q = ⊥` is *weaker* than mathlib's
  `LinearMap.BilinForm.Nondegenerate`/`SeparatingLeft` (injectivity of the polar form); `x²` over
  `𝔽₂` separates them. `IsGPRNondegenerate` is *not* the same as mathlib's
  `QuadraticMap.Nondegenerate`, which also bounds the rank of the polar radical and over a field
  is the `IsGPRNonsingular` condition (`QuadraticForm/NonsingularOverFields.lean`), nor the same as
  `EKM`'s "non-degenerate" (see `QuadraticForm.IsEKMNondegenerate` below).
* `QuadraticForm.IsGPRRegular` : `polarBilin Q` is a *bijection* onto `Module.Dual R M`, not merely
  injective (`SeparatingLeft`/weakly regular only asks injectivity). Equivalently, `polarBilin Q`
  is a mathlib perfect pairing (`QuadraticForm.isGPRRegular_iff_isPerfPair`).
* `QuadraticForm.IsGPRNonsingular` : `radical (Q.baseChangeOfProjective F) = ⊥` for every field `F`
  with `[Algebra R F]` (`GN C.8(e)`). GPR calls this property **non-singular**; readers may know
  the same condition as **non-degenerate**, **ordinary**, or **semiregular**, especially over
  fields (`GPR Exc. 11.37`, Remark (2)).
* `QuadraticForm.IsEKMNondegenerate` : for `Q` over a *field* `F`,
  `radical (Q.baseChangeOfProjective K) = ⊥` for every field `K` with `[Algebra F K]`
  (`EKM Definition 7.17`, condition (1) of `Lemma
  7.16`). Literally the same universal statement as `IsGPRNonsingular` specialized to `R` already a
  field — see `QuadraticForm.isEKMNondegenerate_iff_isGPRNonsingular` below.

## Main results

* `QuadraticForm.IsGPRRegular.isGPRNondegenerate` : regularity implies that the radical vanishes.
* `QuadraticForm.radical_eq_bot_iff_injective_polarBilin` : when `2 ∈ Rˣ`, `Q.radical = ⊥`
  agrees exactly with mathlib's weakly-regular/`Nondegenerate` (`GN (C.8.2)`, non-base-changed
  half). This is what makes `IsGPRNondegenerate` collapse onto mathlib's `Nondegenerate` once `2`
  is invertible, and it needs no base change at all: it is a fact about `Q` over `R` itself.
* `Module.Dual.baseChangeEquivOfProjective` : duals commute with base change for finitely
  generated projective modules (`GPR 9.15`).
* `Module.rankAtStalk_dual` : a finitely generated projective module and its dual have the same
  rank at every stalk.
* `QuadraticForm.IsGPRRegular.isGPRNonsingular` : `Q` regular implies `Q` non-singular for `M`
  finitely generated projective (`GN (C.8.1)`), via
  `QuadraticForm.IsGPRRegular.injective_polarBilin_baseChangeOfProjective` — regularity survives
  base change as injectivity of the polar form.
* `Module.Dual.bijective_of_forall_residue_field_injective` : a map from a finite **free**
  module to its dual that is injective after base change to every residue field is bijective —
  the determinant heart of `GN (C.8.2)`'s converse.
* `QuadraticForm.isGPRRegular_of_forall_baseChangeOfProjective_isGPRRegular` : regularity after
  every field base change implies regularity over the base ring, for a finite projective module.
* `QuadraticForm.IsGPRNonsingular.bijective_baseChange_of_isLocalRing` : the same statement for
  `M` finite projective, after base change to an arbitrary *local* `R`-algebra, where `M` becomes
  free.
* `QuadraticForm.IsGPRNonsingular.isGPRRegular`, `QuadraticForm.isGPRRegular_iff_isGPRNonsingular` :
  `GN (C.8.2)`'s converse (non-singular implies regular when `2 ∈ Rˣ`) and the resulting
  equivalence.
* `QuadraticMap.radical_prod_eq_bot`,
  `QuadraticMap.radical_eq_bot_left_of_radical_prod_eq_bot` : how the radical of an orthogonal sum
  `QuadraticMap.prod` relates to those of its summands, over an arbitrary base ring.
* `QuadraticForm.baseChangeOfProjective_prod` : base change of an orthogonal sum is the orthogonal
  sum of the base changes, along the canonical `A ⊗[R] (M₁ × M₂) ≃ (A ⊗ M₁) × (A ⊗ M₂)`.
* `QuadraticForm.IsGPRNonsingular.of_prod_left`, `.of_prod_right`,
  `QuadraticForm.IsGPRRegular.prod_isGPRNonsingular` : **`GN (C.8.3)`**, the two implications
  relating non-singularity to orthogonal sums. The asymmetry is essential — the second needs `q₁`
  *regular*, not merely non-singular.
* `QuadraticForm.isGPRNonsingular_rankOne`, `QuadraticForm.isGPRRegular_rankOne_iff` : the
  rank-one form `⟨u⟩ : r ↦ u * r ^ 2` is non-singular for `u` a unit, but regular only when
  `2 * u` is one — so `IsGPRNonsingular` is strictly weaker than `IsGPRRegular`, and the
  `2 ∈ Rˣ` hypothesis above is sharp. `QuadraticForm.not_isGPRRegular_rankOne_one_int` is the
  concrete witness over `ℤ`.
* `QuadraticForm.isEKMNondegenerate_iff_isGPRNonsingular` : over a field `R`, `IsEKMNondegenerate`
  and `IsGPRNonsingular` are the same predicate.

All results in this file are complete; there are no `sorry`s.

## Implementation notes

`IsGPRNonsingular` is stated for `M` finitely generated projective over `R`, matching GN's own
definition of a "quadratic form" (finite projectivity of the module is part of the data, not a
separate hypothesis — see the README). It routes through `QuadraticForm.baseChangeOfProjective`
(`QuadraticForm/BaseChangeProjective.lean`), *not* mathlib's `QuadraticForm.baseChange`: the latter
requires `[Invertible (2 : R)]` (built from the halved `QuadraticMap.associated`) and is therefore
inapplicable to exactly the characteristic-2 example (`GPR 19.4`, Layer 8) this development exists
to support — the trap `AGENTS.md` §6(a) is about.

**What is now proved, and how.** `GPR 9.15` is proved in full finite-projective generality:
`Module.Dual.baseChangeEquivOfProjective` identifies
`A ⊗[R] (Module.Dual R M)` with `Module.Dual A (A ⊗[R] M)`. The proof first records naturality
of the canonical comparison map, then writes `M` as a retract of `Fin n → R`. On the finite
free module it uses mathlib's `IsBaseChange.toDualBaseChange`; naturality transports the inverse
across the retract. This is parallel to `HasBilinRepr.of_retract` in
`QuadraticForm/BaseChangeProjective.lean`.

Consequently, `GN (C.8.1)` (`Q` regular implies `Q` non-singular) is proved for every finitely
generated projective `M`, with no freeness hypothesis.

The other piece the free case needed was a compatibility fact between mathlib's
`LinearMap.BilinForm.baseChange` (built via `tensorDistrib`) and the composite of ordinary linear
base change with the dual-comparison map above; that is
`LinearMap.BilinForm.baseChange_eq_comp_dualBaseChange`, proved directly by checking both sides on
pure tensors.

**The converse half of `GN (C.8.2)`, and why it needed care.** Non-singular implies regular is
the classical local-global argument, in three steps, none of them deep:

1. Over a ring where the module is *free*, `polarBilin Q` is a square matrix, and a matrix is
   invertible iff its determinant is a unit iff that determinant lies in no maximal ideal — so
   injectivity after base change to each residue field (which is what non-singularity supplies)
   forces invertibility. That is `Module.Dual.bijective_of_forall_residue_field_injective`.
2. Over a *local* ring `S`, a finite projective `M` becomes free (finite + flat over a local
   ring), so step 1 applies to `S ⊗[R] M`. That is
   `QuadraticForm.IsGPRNonsingular.bijective_baseChange_of_isLocalRing`.
3. A linear map that is bijective after base change to `Localization.AtPrime 𝔪` for every maximal
   `𝔪` is bijective. That is `LinearMap.bijective_of_forall_baseChange_atPrime_bijective`.

Mathematically that is the whole proof, and every step was easy. What made it hard in Lean was
naming residue fields concretely, and the fix in both places was to keep them abstract:

* Step 1's hypothesis is phrased as "for every field `F` with `[Algebra S F]` whose structure map
  has kernel `𝔪`", *not* as "for `S ⧸ 𝔪`". Since `IsGPRNonsingular` accepts any field carrying an
  `R`-algebra structure, and a residue field of `S` carries one via `R → S → F`, step 2 can feed
  it such an `F` with no residue-field identification at all — no
  `IsLocalization.AtPrime.equivQuotMaximalIdeal`, no `IsLocalRing.eq_maximalIdeal`. Had the
  hypothesis kept the concrete `S ⧸ 𝔪`, step 2 would have to elaborate
  `Localization.AtPrime 𝔪 ⧸ 𝔫`, a quotient of a localization, whose `CommSemiring` instance
  diverges against the ring structure underlying `Ideal.Quotient.field 𝔫`; an earlier attempt
  along those lines ran for eight hours without terminating.
* Step 2 is likewise stated for an arbitrary local `R`-algebra `S`, with the localization
  supplied only in the one-line corollary `bijective_baseChange_atPrime`. With `S` a variable,
  `SMul R S` can only be `Algebra.toSMul`, so the `IsScalarTower R S F` the proof builds for a
  residue field typechecks on the nose; at the concrete localization it would have to be
  reconciled with `OreLocalization.instSMulOfIsScalarTower`.

One further instance subtlety, recorded because it is easy to hit again: inside step 1 the
residue field structure on `S ⧸ 𝔪` must be introduced with `letI`, not `haveI`. `hinj`
synthesizes `Field F` first and then wants an `Algebra S F` over *that* semiring structure; an
opaque `haveI` prevents `Field.toSemiring` from unfolding to the quotient's own `CommRing`, and
`Algebra S (S ⧸ 𝔪)` then fails to synthesize outright.

**Sharpness of `2 ∈ Rˣ`.** That hypothesis in `GN (C.8.2)` is not an artifact of the proof:
`QuadraticForm.rankOne`, the form `⟨u⟩ : r ↦ u * r ^ 2` on `R` itself, is non-singular for every
unit `u` (`isGPRNonsingular_rankOne`) but regular exactly when `2 * u` — equivalently `2` — is a
unit (`isGPRRegular_rankOne_iff`, `isGPRRegular_rankOne_iff_isUnit_two`). Over `ℤ` with `u = 1`
this separates the two predicates outright. See the section at the end of this file.

**Comparison with `EKM`.** `GN C.9` identifies non-singularity over a field with EKM's notion of
non-degeneracy. Traced
to source: `GN` cites `EKM Definition 7.17`, which in turn rests on `EKM Lemma 7.16`. Unlike `GPR`
and `GN`, `EKM` only ever works with quadratic forms over a *field*, never over a general
commutative ring — so its terminology only competes with `GPR`'s once `R` is specialized to a
field, and any Lean statement relating the two must carry that hypothesis explicitly rather than
silently inheriting it. For a quadratic form `ϕ` over a field `F` with polar form `b_ϕ`, `EKM`
write `rad ϕ := {v ∈ rad b_ϕ : ϕ(v) = 0}` — precisely mathlib's `QuadraticMap.radical` — and call
`ϕ` **regular** if `rad ϕ = 0`.

⚠ **This is a third name for our `IsGPRNondegenerate`, not for `IsGPRRegular`.** `EKM`'s "regular"
means `rad ϕ = 0`, matching `QuadraticForm.IsGPRNondegenerate`, *not* the bijective-polar-form
`QuadraticForm.IsGPRRegular` above — a second, independent collision on top of the
"non-degenerate" one already noted, both worth getting right before formalizing `EKM`'s statements
here.

`EKM Lemma 7.16` shows TFAE: (1) `ϕ_K` is `EKM`-regular for every field extension `K/F`;
(2) `ϕ_K` is `EKM`-regular for some algebraically closed `K ⊇ F`; (3) `ϕ` is `EKM`-regular and
`dim (rad b_ϕ) ≤ 1`. `Definition 7.17` calls `ϕ` **non-degenerate** when these hold; this is
`QuadraticForm.IsEKMNondegenerate` below, defined via condition (1) since it is the one that reads
verbatim as a base-change statement. When `R` is already a field, condition (1) is literally
`IsGPRNonsingular Q` (`Algebra R F` for `F` a field is automatically a field extension of `R`,
field homomorphisms being injective) — the two quantify over exactly the same class of base
changes — which is `QuadraticForm.isEKMNondegenerate_iff_isGPRNonsingular` below. That equality of
predicates is immediate from the definitions. `EKM Lemma 7.16` itself (that conditions (1)–(3)
agree) is proved in `QuadraticForm/NonsingularOverFields.lean`, by `EKM`'s own elementary
argument rather than by `GN`'s `C.9`, whose proof cites an external étale-cover argument `GN`
does not reprove and which `AGENTS.md` §8 asks us not to import wholesale. That file also proves
`GPR Exercise 11.37` and most of its Remark (1).

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, Cambridge
  University Press, New Mathematical Monographs vol. 48, 2024.  11.11, 19.4.
* [GPR 42] Calmès, Fasel, *Groupes classiques*, Panoramas & Synthèses **46** (2015),
  1–133.
* [GPR 53] Conrad, *Reductive group schemes*, in *Autour des schémas en groupes*, vol. I,
  Panoramas & Synthèses **42/43** (2014), 93–444.
* [GPR 60] Deligne, Katz, *Groupes de Monodromie en Géométrie Algébrique: Séminaire de
  Géométrie Algébrique du Bois-Marie 1967–1969 (SGA 7 II)*, vol. 340, Springer, 2006.
* [GPR 157] Knus, *Quadratic and Hermitian Forms over Rings*, vol. 294, Springer-Verlag, 1991.
* [GN] Gille, Neher, *Group schemes over LG-rings and applications to cancellation theorems and
  Azumaya algebras*, European Journal of Mathematics **11** (2025), article 42, Appendix C
  (`C.8`, `C.9`).
* [EKM] Elman, Karpenko, Merkurjev, *The Algebraic and Geometric Theory of Quadratic Forms*,
  AMS Colloquium Publications vol. 56, 2008. §7.A, Lemma 7.16, Definition 7.17.
-/

universe u v w s t₁ t₂ t₃

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
  {N : Type w} [AddCommGroup N] [Module R N]

/-- `Q` is **non-degenerate** in GPR's sense (`GPR 11.11`, boundary/trap in `AGENTS.md` §6(b)):
`QuadraticMap.radical Q = ⊥`. This is a genuinely different, *weaker* notion than mathlib's
`polarBilin.Nondegenerate` (GPR's "weakly regular"), which asks the polar form itself to be
injective: the radical lies in the kernel of the polar form, so an injective polar form forces
`radical Q = ⊥`, but not conversely — `x²` over `𝔽₂` has zero polar form and zero radical.

The radical itself is mathlib's `QuadraticMap.radical` — the submodule of vectors on which both
`Q` and its polar form vanish (`GN C.8(d)`, `EKM` Chapter II §7). Constraining `Q` itself, not
just the polar form, is what makes it smaller than the kernel of the polar form, which is all that
mathlib's bilinear-form nondegeneracy predicates see — see `AGENTS.md` §6(b).

**Terminology.** Named for its source, `GPR`, since `EKM` uses "non-degenerate" for a different,
stronger condition — see `QuadraticForm.IsEKMNondegenerate` below. Note in particular that this
is *not* mathlib's `QuadraticMap.Nondegenerate`, which additionally bounds the rank of the polar
radical and over a field is the `IsGPRNonsingular` condition; see
`QuadraticForm/NonsingularOverFields.lean`. -/
def QuadraticForm.IsGPRNondegenerate (Q : QuadraticForm R M) : Prop :=
  Q.radical = ⊥

/-- `Q` is **regular**: its polar form is a *bijection* `M ≃ Module.Dual R M`, not merely
injective. The strongest of `GPR 11.11`'s notions: it implies the other three (non-singularity
for `M` finitely generated projective).

**Terminology.** Named for its source, `GPR`, since `EKM` uses "regular" for the weaker condition
`radical Q = ⊥` — see `QuadraticForm.IsEKMNondegenerate` below. -/
def QuadraticForm.IsGPRRegular (Q : QuadraticForm R M) : Prop :=
  Function.Bijective (QuadraticMap.polarBilin Q : M →ₗ[R] Module.Dual R M)

/-- **`GPR`'s regularity is mathlib's perfect pairing**: `Q` is regular exactly when its polar form
is a `LinearMap.IsPerfPair`. The polar form is symmetric, so bijectivity in one argument already
gives it in the other. This opens mathlib's perfect-pairing API to regular forms. -/
theorem QuadraticForm.isGPRRegular_iff_isPerfPair {Q : QuadraticForm R M} :
    Q.IsGPRRegular ↔ (QuadraticMap.polarBilin Q).IsPerfPair := by
  have hflip : (QuadraticMap.polarBilin Q).flip = QuadraticMap.polarBilin Q :=
    LinearMap.ext₂ fun x y ↦ QuadraticMap.polar_comm Q y x
  refine ⟨fun h ↦ ⟨h, by rw [hflip]; exact h⟩, fun h ↦ h.1⟩

/-- A regular quadratic form is non-degenerate in `GPR`'s sense: its radical lies in the kernel
of the polar map, and that kernel vanishes because the polar map is injective. -/
theorem QuadraticForm.IsGPRRegular.isGPRNondegenerate {Q : QuadraticForm R M}
    (h : Q.IsGPRRegular) : Q.IsGPRNondegenerate := by
  rw [QuadraticForm.IsGPRNondegenerate]
  exact le_antisymm
    (QuadraticMap.radical_le_ker_polarBilin.trans_eq (LinearMap.ker_eq_bot.mpr h.1)) bot_le

/-- `Q` is **non-singular** (`GN C.8(e)`): its radical vanishes after base change to every field
extension of `R`. Uses `QuadraticForm.baseChangeOfProjective`
(`QuadraticForm/BaseChangeProjective.lean`), which needs no hypothesis on `2`.

**Terminology.** Named for its source, `GPR`. GPR's Remark (2) following Exercise 11.37 notes that
this condition is called **non-degenerate** in `[GPR 53, §6.1 and Exercise 1.6.10]`, **ordinary**
in `[GPR 60, §XII.1]`, and **semiregular** in `[GPR 157, §IV.3]` or `[GPR 42, §2.6]`. Thus,
over a field, a reader may have met GPR's "non-singular" quadratic forms under any of those names.
Here
**non-degenerate** in that literature-synonym sense must not be confused with either
`QuadraticForm.IsGPRNondegenerate` above (the `radical Q = ⊥` rung over the base ring) or mathlib's
`LinearMap.BilinForm.Nondegenerate` (GPR's "weakly regular": an injective polar form). When `R` is
already a field, this condition coincides with `EKM`'s own "non-degenerate" —
`QuadraticForm.IsEKMNondegenerate` below. -/
def QuadraticForm.IsGPRNonsingular [Module.Finite R M] [Module.Projective R M]
    (Q : QuadraticForm R M) : Prop :=
  ∀ (F : Type*) [Field F] [Algebra R F], (Q.baseChangeOfProjective F).radical = ⊥

/-- When `2` is invertible, `radical Q = ⊥` (GPR's non-degenerate) agrees exactly with
mathlib's `polarBilin.Nondegenerate`/`SeparatingLeft` (GPR's weakly regular) —
`GN (C.8.2)`'s non-base-changed half. No base change is involved:
`2 • Q m = polar Q m m` lets `Q m = 0` be recovered from the polar form vanishing, so the
extra `Q m = 0` clause in the radical becomes redundant. That last step is mathlib's
`QuadraticMap.radical_eq_ker_polarBilin`. -/
theorem QuadraticForm.radical_eq_bot_iff_injective_polarBilin [Invertible (2 : R)]
    (Q : QuadraticForm R M) :
    Q.radical = ⊥ ↔ Function.Injective (QuadraticMap.polarBilin Q) := by
  rw [QuadraticMap.radical_eq_ker_polarBilin, LinearMap.ker_eq_bot]

open scoped TensorProduct

namespace Module.Dual

variable {A : Type*} [CommRing A] [Algebra R A]

variable (A) in
/-- The canonical comparison map from the base change of the dual to the dual of the base change.
On pure tensors it sends `a ⊗ₜ f` to the functional
`b ⊗ₜ m ↦ a * b * algebraMap R A (f m)`.

No finiteness or projectivity hypothesis is needed to define this map. Those hypotheses enter in
`Module.Dual.baseChangeEquivOfProjective`, where `GPR 9.15` says that it is an equivalence. -/
noncomputable def baseChangeTensor :
    A ⊗[R] Module.Dual R M →ₗ[A] Module.Dual A (A ⊗[R] M) where
  toAddHom := (TensorProduct.lift {
    toFun a := a • Module.Dual.baseChange (R := R) (V := M) A
    map_add' a b := by simp [add_smul]
    map_smul' r a := by simp }).toAddHom
  map_smul' a g := by
    induction g using TensorProduct.inductionOn with
    | add x y hx hy => aesop
    | tmul b f => simp [TensorProduct.smul_tmul', mul_smul]

/-- The value of the canonical dual-base-change comparison map on two pure tensors. -/
@[simp]
theorem baseChangeTensor_tmul (a : A) (f : Module.Dual R M) (b : A) (m : M) :
    baseChangeTensor (R := R) A (a ⊗ₜ[R] f) (b ⊗ₜ[R] m) =
      a * b * algebraMap R A (f m) := by
  change (a • Module.Dual.baseChange (R := R) (V := M) A f) (b ⊗ₜ[R] m) = _
  rw [show (b ⊗ₜ[R] m : A ⊗[R] M) = b • (1 ⊗ₜ[R] m) by
    simp [TensorProduct.smul_tmul', smul_eq_mul]]
  simp [Module.Dual.baseChange_apply_tmul, Algebra.smul_def, mul_assoc, mul_comm]
  ac_rfl

/-- The canonical dual-base-change comparison map is natural in the module. -/
theorem baseChangeTensor_naturality {P : Type w} [AddCommGroup P] [Module R P]
    (f : M →ₗ[R] P) :
    baseChangeTensor (R := R) A ∘ₗ LinearMap.baseChange A f.dualMap =
      (LinearMap.baseChange A f).dualMap ∘ₗ baseChangeTensor (R := R) A := by
  ext g m
  simp

/-- On a finite free module, `baseChangeTensor` is the comparison equivalence already supplied by
mathlib's `IsBaseChange.toDualBaseChange`. -/
theorem baseChangeTensor_eq_toDualBaseChange [Module.Free R M] [Module.Finite R M] :
    baseChangeTensor (R := R) A =
      (TensorProduct.isBaseChange R M A).toDualBaseChange.toLinearMap := by
  ext f m
  simp only [TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
    LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
  rw [baseChangeTensor_tmul]
  simpa using (IsBaseChange.toDualBaseChange_tmul
    (TensorProduct.isBaseChange R M A) 1 f m).symm

/-- **`GPR 9.15`.** For a finitely generated projective module, the canonical comparison map
`A ⊗[R] (Module.Dual R M) → Module.Dual A (A ⊗[R] M)` is bijective.

The proof writes `M` as a retract of a finite free module. Naturality of `baseChangeTensor`
transports the inverse of mathlib's finite-free comparison map across the retraction. -/
theorem baseChangeTensor_bijective_of_projective [Module.Finite R M]
    [Module.Projective R M] :
    Function.Bijective (baseChangeTensor (R := R) (M := M) A) := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' R M
  obtain ⟨i, hri⟩ := r.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hr)
  let P := Fin n → R
  let eP := (TensorProduct.isBaseChange R P A).toDualBaseChange
  let inverse : Module.Dual A (A ⊗[R] M) →ₗ[A] A ⊗[R] Module.Dual R M :=
    LinearMap.baseChange A i.dualMap ∘ₗ eP.symm.toLinearMap ∘ₗ
      (LinearMap.baseChange A r).dualMap
  have heP : baseChangeTensor (R := R) (M := P) A = eP.toLinearMap :=
    baseChangeTensor_eq_toDualBaseChange
  have hTensorDual :
      LinearMap.baseChange A i.dualMap ∘ₗ LinearMap.baseChange A r.dualMap =
        LinearMap.id := by
    rw [← LinearMap.baseChange_comp, LinearMap.dualMap_comp_dualMap, hri,
      LinearMap.dualMap_id, LinearMap.baseChange_id]
  have hBase : LinearMap.baseChange A r ∘ₗ LinearMap.baseChange A i = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, hri, LinearMap.baseChange_id]
  have hBaseDual :
      (LinearMap.baseChange A i).dualMap ∘ₗ (LinearMap.baseChange A r).dualMap =
        LinearMap.id := by
    rw [LinearMap.dualMap_comp_dualMap, hBase, LinearMap.dualMap_id]
  have hinvLeft : Function.LeftInverse inverse (baseChangeTensor (R := R) A) := by
    intro x
    simp only [inverse, LinearMap.comp_apply]
    have hnat := LinearMap.congr_fun
      (baseChangeTensor_naturality (R := R) (A := A) (M := P) r) x
    simp only [LinearMap.comp_apply] at hnat
    rw [← hnat, heP]
    calc
      _ = LinearMap.baseChange A i.dualMap (LinearMap.baseChange A r.dualMap x) :=
        congrArg (LinearMap.baseChange A i.dualMap) (eP.symm_apply_apply _)
      _ = x := by
        simpa using DFunLike.congr_fun hTensorDual x
  have hinvRight : Function.RightInverse inverse (baseChangeTensor (R := R) A) := by
    intro y
    simp only [inverse, LinearMap.comp_apply]
    have hnat := LinearMap.congr_fun
      (baseChangeTensor_naturality (R := R) (A := A) (M := M) i)
      (eP.symm ((LinearMap.baseChange A r).dualMap y))
    simp only [LinearMap.comp_apply] at hnat
    calc
      _ = (LinearMap.baseChange A i).dualMap
          (baseChangeTensor (R := R) (M := P) A
            (eP.symm ((LinearMap.baseChange A r).dualMap y))) := hnat
      _ = (LinearMap.baseChange A i).dualMap ((LinearMap.baseChange A r).dualMap y) := by
        rw [heP]
        exact congrArg (LinearMap.baseChange A i).dualMap (eP.apply_symm_apply _)
      _ = y := by
        simpa using DFunLike.congr_fun hBaseDual y
  exact ⟨hinvLeft.injective, hinvRight.surjective⟩

/-- **`GPR 9.15`.** Taking the dual of a finitely generated projective module commutes with
arbitrary base change. -/
noncomputable def baseChangeEquivOfProjective [Module.Finite R M] [Module.Projective R M] :
    A ⊗[R] Module.Dual R M ≃ₗ[A] Module.Dual A (A ⊗[R] M) :=
  LinearEquiv.ofBijective (baseChangeTensor (R := R) (M := M) A)
    (baseChangeTensor_bijective_of_projective (R := R) (A := A) (M := M))

/-- The projective dual-base-change equivalence has `baseChangeTensor` as its underlying map. -/
@[simp]
theorem baseChangeEquivOfProjective_apply [Module.Finite R M] [Module.Projective R M]
    (x : A ⊗[R] Module.Dual R M) :
    baseChangeEquivOfProjective (R := R) (M := M) (A := A) x =
      baseChangeTensor (R := R) A x :=
  rfl

end Module.Dual

/-- A finitely generated projective module and its dual have the same rank at every stalk. This
is the rank consequence of `GPR 9.15`. -/
theorem Module.rankAtStalk_dual [Module.Finite R M] [Module.Projective R M] :
    Module.rankAtStalk (R := R) (Module.Dual R M) = Module.rankAtStalk M := by
  ext p
  rw [Module.rankAtStalk_eq_finrank_tensorProduct,
    (Module.Dual.baseChangeEquivOfProjective (R := R) (M := M)
      (A := Localization.AtPrime p.asIdeal)).finrank_eq]
  let : Module.Free (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime p.asIdeal ⊗[R] M) := Module.free_of_flat_of_isLocalRing
  rw [← (Module.Free.chooseBasis (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime p.asIdeal ⊗[R] M)).toDualEquiv.finrank_eq,
    ← Module.rankAtStalk_eq_finrank_tensorProduct]

namespace Module.Dual

/-- If a linear map from a finite free module into its own dual is injective after base change
to every residue field of the base ring, it is bijective. Used for the base-changed half of
`GN (C.8.2)` (`QuadraticForm.IsGPRNonsingular.isGPRRegular` below), applied after localizing at
each maximal ideal.

The matrix of the map, computed in a chosen basis and its dual basis, has determinant that cannot
lie in any maximal ideal: its image in each residue field is the determinant of a matrix
representing an injective — hence, by a dimension count, bijective — map, so is nonzero. Hence the
determinant is a unit, and a unit-determinant map is bijective.

**The residue field is kept abstract**, presented as any field `F` with `[Algebra S F]` whose
structure map has kernel `𝔪`, rather than as the concrete `S ⧸ 𝔪`. Only the kernel condition is
used (to see that a determinant lying in `𝔪` dies in `F`), and the proof instantiates `F` at
`S ⧸ 𝔪` internally — where `S` is still an abstract ring, so nothing expensive is formed. The
payoff is at the call site: `QuadraticForm.IsGPRNonsingular.bijective_baseChange_atPrime` below
instantiates `S` at `Localization.AtPrime 𝔪`, and the concrete form of this hypothesis would
force Lean to elaborate `Localization.AtPrime 𝔪 ⧸ 𝔫` — a quotient of a localization, whose
`CommSemiring` instance search diverges against the one under `Ideal.Quotient.field 𝔫`. With `F`
abstract that term never appears, and `IsGPRNonsingular` — which accepts *any* field carrying an
`R`-algebra structure, in particular `F` via `R → S → F` — applies directly, with no residue-field
identification needed at all. `F` shares `S`'s universe because the internal instantiation at
`S ⧸ 𝔪` lives there. -/
theorem bijective_of_forall_residue_field_injective {S : Type s} [CommRing S]
    {P : Type*} [AddCommGroup P] [Module S P] {ι : Type*} [Finite ι]
    (v : Basis ι S P) {g : P →ₗ[S] Module.Dual S P}
    (hinj : ∀ (𝔪 : Ideal S) [𝔪.IsMaximal] (F : Type s) [Field F] [Algebra S F],
      RingHom.ker (algebraMap S F) = 𝔪 → Function.Injective (LinearMap.baseChange F g)) :
    Function.Bijective g := by
  -- The matrix and determinant below need `Fintype ι` and `DecidableEq ι`; neither appears in the
  -- statement, so both are recovered here.
  cases nonempty_fintype ι
  classical
  have hUnit : IsUnit (LinearMap.toMatrix v v.dualBasis g).det := by
    by_contra hnot
    obtain ⟨𝔪, hmax, hmem⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.mpr hnot)
    have := hmax
    -- `letI`, not `haveI`: `hinj` synthesizes `Field F` first and then demands an `Algebra S F`
    -- built on *that* semiring structure. An opaque `haveI` blocks `Field.toSemiring` from
    -- unfolding to the quotient's own `CommRing`, and `Algebra S (S ⧸ 𝔪)` then fails to
    -- synthesize.
    let : Field (S ⧸ 𝔪) := Ideal.Quotient.field 𝔪
    set A : Matrix ι ι S := LinearMap.toMatrix v v.dualBasis g with hA
    set B : Matrix ι ι (S ⧸ 𝔪) := A.map (algebraMap S (S ⧸ 𝔪)) with hB
    have hBdet : B.det = 0 := by
      rw [hB, ← RingHom.mapMatrix_apply, ← RingHom.map_det, Ideal.Quotient.algebraMap_eq,
        Ideal.Quotient.eq_zero_iff_mem]
      exact hmem
    obtain ⟨y, hy, hBy⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hBdet
    set b1 := Algebra.TensorProduct.basis (S ⧸ 𝔪) v with hb1
    set b2 := Algebra.TensorProduct.basis (S ⧸ 𝔪) v.dualBasis with hb2
    have hBeq : B = LinearMap.toMatrix b1 b2 (LinearMap.baseChange (S ⧸ 𝔪) g) := by
      rw [hB, hA, LinearMap.toMatrix_baseChange]
    set x : (S ⧸ 𝔪) ⊗[S] P := b1.equivFun.symm y with hx
    have hrepr : ⇑(b1.repr x) = y := by
      rw [hx, ← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    have hxne : x ≠ 0 := by
      intro h
      apply hy
      have : ⇑(b1.repr x) = ⇑(b1.repr (0 : (S ⧸ 𝔪) ⊗[S] P)) := by rw [h]
      rw [hrepr, map_zero] at this
      simpa using this
    have hz : B.toLin b1 b2 x = 0 := by
      rw [Matrix.toLin_apply_eq_zero_iff]
      intro j
      have hj := congrFun hBy j
      rwa [hrepr]
    rw [hBeq, Matrix.toLin_toMatrix] at hz
    have hker : RingHom.ker (algebraMap S (S ⧸ 𝔪)) = 𝔪 := by
      rw [Ideal.Quotient.algebraMap_eq]; exact Ideal.mk_ker
    apply hxne
    apply hinj 𝔪 (S ⧸ 𝔪) hker
    rw [map_zero]
    exact hz
  exact (LinearEquiv.ofIsUnitDet (v := v) (v' := v.dualBasis) hUnit).bijective

end Module.Dual

/-- A linear map between two `R`-modules is bijective if it becomes bijective after base change
to the localization at every maximal ideal of `R`. Bridges `bijective_of_localized_maximal`
(stated for the concrete `LocalizedModule` localization) to base change along
`Localization.AtPrime`, via the natural equivalence `LocalizedModule.equivTensorProduct`. -/
theorem LinearMap.bijective_of_forall_baseChange_atPrime_bijective {R : Type*} [CommRing R]
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (f : M →ₗ[R] N)
    (h : ∀ (𝔪 : Ideal R) [𝔪.IsMaximal],
      Function.Bijective (LinearMap.baseChange (Localization.AtPrime 𝔪) f)) :
    Function.Bijective f := by
  apply bijective_of_localized_maximal f
  intro 𝔪 hmax
  have hsq : (LocalizedModule.equivTensorProduct 𝔪.primeCompl N) ∘
      (LocalizedModule.map 𝔪.primeCompl f) =
      (LinearMap.baseChange (Localization.AtPrime 𝔪) f) ∘
      (LocalizedModule.equivTensorProduct 𝔪.primeCompl M) := by
    ext m
    induction m using LocalizedModule.induction_on with
    | _ x s =>
      simp [LocalizedModule.map_mk, LocalizedModule.equivTensorProduct_apply_mk,
        LinearMap.baseChange_tmul]
  have hbij : Function.Bijective (LinearMap.baseChange (Localization.AtPrime 𝔪) f) := h 𝔪
  have hcomp : Function.Bijective ((LocalizedModule.equivTensorProduct 𝔪.primeCompl N) ∘
      (LocalizedModule.map 𝔪.primeCompl f)) := by
    rw [hsq]
    exact hbij.comp (LocalizedModule.equivTensorProduct 𝔪.primeCompl M).bijective
  exact (Function.Bijective.of_comp_iff'
    (LocalizedModule.equivTensorProduct 𝔪.primeCompl N).bijective _).mp hcomp

/-- The base change of a bilinear form (`LinearMap.BilinForm.baseChange`, built via
`tensorDistrib`) agrees with base-changing it as a linear map into the dual and then applying the
dual-base-change equivalence from `GPR 9.15`. Checked directly on pure tensors. -/
theorem LinearMap.BilinForm.baseChange_eq_comp_dualBaseChange [Module.Projective R M]
    [Module.Finite R M] (A : Type*) [CommRing A] [Algebra R A] (B : LinearMap.BilinForm R M) :
    LinearMap.BilinForm.baseChange A B =
      (Module.Dual.baseChangeEquivOfProjective (R := R) (M := M) (A := A)).toLinearMap ∘ₗ
        LinearMap.baseChange A B := by
  ext a m
  simp only [TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
    LinearMap.coe_restrictScalars, LinearMap.BilinForm.baseChange_tmul, mul_one,
    LinearMap.restrictScalars_comp, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearMap.baseChange_tmul]
  have hkey := Module.Dual.baseChangeTensor_tmul (R := R) (A := A) 1 (B a) 1 m
  simp only [one_mul] at hkey
  rw [Module.Dual.baseChangeEquivOfProjective_apply, hkey,
    Algebra.algebraMap_eq_smul_one]

/-- A quadratic form on a finite projective module is regular if it becomes regular after base
change to every field over the base ring.

This is the local-global principle for the polar map. After localizing at a maximal ideal, the
module becomes finite free. The polar map is then bijective by Nakayama's lemma because its base
change to every residue field is injective; the latter is the assumed regularity after the
corresponding composite field extension of `R`. -/
theorem QuadraticForm.isGPRRegular_of_forall_baseChangeOfProjective_isGPRRegular
    [Module.Projective R M] [Module.Finite R M] (Q : QuadraticForm R M)
    (h : ∀ (F : Type u) [Field F] [Algebra R F],
      (Q.baseChangeOfProjective F).IsGPRRegular) : Q.IsGPRRegular := by
  apply LinearMap.bijective_of_forall_baseChange_atPrime_bijective
  intro 𝔪 _
  let S := Localization.AtPrime 𝔪
  let : Module.Flat R M := Module.Flat.of_projective
  let : Module.Finite S (S ⊗[R] M) := Module.Finite.base_change R S M
  let : Module.Free S (S ⊗[R] M) := Module.free_of_flat_of_isLocalRing
  let v : Module.Basis (Module.Free.ChooseBasisIndex S (S ⊗[R] M)) S (S ⊗[R] M) :=
    Module.Free.chooseBasis S (S ⊗[R] M)
  let f : M →ₗ[R] Module.Dual R M := QuadraticMap.polarBilin Q
  let g : (S ⊗[R] M) →ₗ[S] Module.Dual S (S ⊗[R] M) :=
    (Module.Dual.baseChangeEquivOfProjective (R := R) (M := M) (A := S)).toLinearMap ∘ₗ
      LinearMap.baseChange S f
  have hgbij : Function.Bijective g := by
    apply Module.Dual.bijective_of_forall_residue_field_injective v (g := g)
    intro 𝔫 _ F _ _ _
    let : Algebra R F := ((algebraMap S F).comp (algebraMap R S)).toAlgebra
    have : IsScalarTower R S F := IsScalarTower.of_algebraMap_eq' rfl
    have hdirect : Function.Injective (LinearMap.baseChange F f) := by
      have hpolar := (h F).injective
      rw [QuadraticForm.polarBilin_baseChangeOfProjective,
        LinearMap.BilinForm.baseChange_eq_comp_dualBaseChange] at hpolar
      simp only [LinearMap.coe_comp] at hpolar
      simpa only [f] using hpolar.of_comp
    have hiter : Function.Injective
        (LinearMap.baseChange F (LinearMap.baseChange S f)) := by
      rw [LinearMap.baseChange_baseChange f]
      exact (TensorProduct.AlgebraTensorModule.cancelBaseChange R S F F
        (Module.Dual R M)).symm.injective.comp
        (hdirect.comp (TensorProduct.AlgebraTensorModule.cancelBaseChange R S F F M).injective)
    simp only [g, LinearMap.baseChange_comp]
    have hE : Function.Injective (LinearMap.baseChange F
        (Module.Dual.baseChangeEquivOfProjective
          (R := R) (M := M) (A := S)).toLinearMap) := by
      rw [← LinearEquiv.coe_baseChange]
      exact LinearEquiv.injective _
    exact hE.comp hiter
  exact (Function.Bijective.of_comp_iff'
    (Module.Dual.baseChangeEquivOfProjective (R := R) (M := M) (A := S)).bijective
    (LinearMap.baseChange S f)).mp hgbij

/-- **Regularity is stable under base change.** Base-changing the bijection
`polarBilin Q : M ≃ Module.Dual R M` as a plain linear map keeps it injective, and composing with
the always-bijective dual-comparison map of `GPR 9.15`
(`LinearMap.BilinForm.baseChange_eq_comp_dualBaseChange`) identifies the result with the polar
form of the base-changed quadratic form. -/
theorem QuadraticForm.IsGPRRegular.injective_polarBilin_baseChangeOfProjective
    [Module.Projective R M] [Module.Finite R M] {Q : QuadraticForm R M} (hReg : Q.IsGPRRegular)
    (A : Type*) [CommRing A] [Algebra R A] :
    Function.Injective (QuadraticMap.polarBilin (Q.baseChangeOfProjective A)) := by
  have hinj1 : Function.Injective (LinearMap.baseChange A (QuadraticMap.polarBilin Q)) :=
    ((LinearEquiv.ofBijective (QuadraticMap.polarBilin Q) hReg).baseChange
      R A M (Module.Dual R M)).injective
  have hinj2 : Function.Injective
      (Module.Dual.baseChangeEquivOfProjective (R := R) (M := M) (A := A)).toLinearMap :=
    (Module.Dual.baseChangeEquivOfProjective (R := R) (M := M) (A := A)).injective
  intro x y hxy
  refine hinj2.comp hinj1 ?_
  rw [QuadraticForm.polarBilin_baseChangeOfProjective,
    LinearMap.BilinForm.baseChange_eq_comp_dualBaseChange] at hxy
  simpa using hxy

/-- **`GN (C.8.1)`.** `Q` regular implies `Q` non-singular: over every field the polar form of the
base change stays injective (`IsGPRRegular.injective_polarBilin_baseChangeOfProjective`), which is
exactly what a vanishing radical needs. -/
theorem QuadraticForm.IsGPRRegular.isGPRNonsingular [Module.Projective R M] [Module.Finite R M]
    {Q : QuadraticForm R M} (hReg : Q.IsGPRRegular) : Q.IsGPRNonsingular := fun F _ _ ↦
  ((Q.baseChangeOfProjective F).radical.eq_bot_iff).mpr fun _ hx ↦
    (injective_iff_map_eq_zero _).mp
      (hReg.injective_polarBilin_baseChangeOfProjective F) _ hx.2

/-- **Non-singularity is stable under base change.** This is the whole point of quantifying over
every field in `R`-alg rather than asking for `radical Q = ⊥` over `R` itself: a field over `S` is
a field over `R`, and `QuadraticForm.baseChangeOfProjectiveIsometryEquiv` identifies the iterated
base change `(Q_S)_F` with the direct one `Q_F`, whose radical vanishes by hypothesis.

The `Algebra R F` and `IsScalarTower R S F` instances are built inside the proof from
`Algebra R S` and `Algebra S F`; they are not available to instance search, and the whole
statement would be false-by-elaboration if `F` carried an unrelated `R`-algebra structure. -/
theorem QuadraticForm.IsGPRNonsingular.baseChangeOfProjective [Module.Finite R M]
    [Module.Projective R M] {Q : QuadraticForm R M} (hNS : Q.IsGPRNonsingular.{u, v, w})
    (S : Type s) [CommRing S] [Algebra R S] :
    (Q.baseChangeOfProjective S).IsGPRNonsingular.{s, max v s, w} := by
  intro F _ _
  let : Algebra R F := ((algebraMap S F).comp (algebraMap R S)).toAlgebra
  have : IsScalarTower R S F := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have he := (QuadraticForm.baseChangeOfProjectiveIsometryEquiv S F Q).map_radical
  rw [hNS F, Submodule.map_eq_bot_iff] at he
  exact he

/-- If `Q` is non-singular, `polarBilin Q` stays injective after base change to any field `F`
with `Invertible (2 : F)`. The field-level half of the translation between `IsGPRNonsingular` and
injectivity of `polarBilin`, isolated at the top level (rather than nested inside
`QuadraticForm.IsGPRNonsingular.isGPRRegular`'s proof) to keep its elaboration cheap. -/
theorem QuadraticForm.IsGPRNonsingular.injective_baseChange [Module.Finite R M]
    [Module.Projective R M] {Q : QuadraticForm R M} (hNS : Q.IsGPRNonsingular.{u, v, u})
    {F : Type u} [Field F] [Algebra R F] [Invertible (2 : F)] :
    Function.Injective
      (LinearMap.baseChange F (QuadraticMap.polarBilin Q : M →ₗ[R] Module.Dual R M)) := by
  have hrad : (Q.baseChangeOfProjective F).radical = ⊥ := hNS F
  have hpolarinj : Function.Injective (QuadraticMap.polarBilin (Q.baseChangeOfProjective F)) :=
    (QuadraticForm.radical_eq_bot_iff_injective_polarBilin _).mp hrad
  rw [QuadraticForm.polarBilin_baseChangeOfProjective,
    LinearMap.BilinForm.baseChange_eq_comp_dualBaseChange] at hpolarinj
  simp only [LinearMap.coe_comp] at hpolarinj
  exact hpolarinj.of_comp

/-- Iterating `injective_baseChange` through an intermediate ring `S`: if `Q` is non-singular,
`polarBilin Q` base-changed to `S` and then to a further `S`-algebra field `F` stays injective.
`LinearMap.baseChange_baseChange` identifies the iterated base change with the direct one to `F`
(an `R`-algebra via `R → S → F`), where `injective_baseChange` applies.

`F` is kept fully generic (a bare `{F : Type u} [Field F] [Algebra S F] [IsScalarTower R S F]`),
rather than fixed to a concrete `S ⧸ 𝔫`: baking a concrete quotient into the statement fixes
*some* `CommSemiring F` instance for `LinearMap.baseChange` the moment the statement is
elaborated, and separately deriving `[Field F]` from `[𝔫.IsMaximal]` inside the proof gives a
second, propositionally-but-not-definitionally-equal instance — reconciling the two costs an
expensive `isDefEq` on every use of `Q.baseChangeOfProjective F`. Keeping `F` abstract sidesteps
the diamond; callers instantiate it (e.g. at `S ⧸ 𝔫`) themselves. -/
theorem QuadraticForm.IsGPRNonsingular.injective_baseChange_baseChange [Module.Finite R M]
    [Module.Projective R M] {Q : QuadraticForm R M}
    (hNS : Q.IsGPRNonsingular.{u, v, u}) {S : Type u} [CommRing S] [Algebra R S]
    {F : Type u} [Field F] [Algebra S F] [Algebra R F] [IsScalarTower R S F]
    [Invertible (2 : F)] :
    Function.Injective (LinearMap.baseChange F
      (LinearMap.baseChange S (QuadraticMap.polarBilin Q : M →ₗ[R] Module.Dual R M))) := by
  set f : M →ₗ[R] Module.Dual R M := QuadraticMap.polarBilin Q with hf
  have hFinj : Function.Injective (LinearMap.baseChange F f) := by
    have hrad : (Q.baseChangeOfProjective F).radical = ⊥ := hNS F
    have hpolarinj : Function.Injective (QuadraticMap.polarBilin (Q.baseChangeOfProjective F)) :=
      (QuadraticForm.radical_eq_bot_iff_injective_polarBilin _).mp hrad
    rw [QuadraticForm.polarBilin_baseChangeOfProjective,
      LinearMap.BilinForm.baseChange_eq_comp_dualBaseChange] at hpolarinj
    simp only [LinearMap.coe_comp] at hpolarinj
    exact hpolarinj.of_comp
  have hbc : LinearMap.baseChange F (LinearMap.baseChange S f) =
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R S F F (Module.Dual R M)).symm ∘ₗ
        LinearMap.baseChange F f ∘ₗ
        (TensorProduct.AlgebraTensorModule.cancelBaseChange R S F F M) :=
    LinearMap.baseChange_baseChange f
  rw [hbc]
  exact (TensorProduct.AlgebraTensorModule.cancelBaseChange R S F F
    (Module.Dual R M)).symm.injective.comp
    (hFinj.comp (TensorProduct.AlgebraTensorModule.cancelBaseChange R S F F M).injective)

/-- Over *any* local `R`-algebra `S`, `polarBilin Q` becomes bijective after base change: a finite
projective `M` is free after base change to a local ring (`M` projective ⇒ flat,
`Module.Flat.of_projective`; finite flat over a local ring is free,
`Module.free_of_flat_of_isLocalRing`), so
`Module.Dual.bijective_of_forall_residue_field_injective` applies to the resulting free module,
with `injective_baseChange_baseChange` supplying its hypothesis at each residue field.

`S` is deliberately kept abstract rather than fixed to `Localization.AtPrime 𝔪` (that is
`bijective_baseChange_atPrime` below, an immediate corollary). With `S` a variable, `SMul R S`
can only be `Algebra.toSMul`, so the `IsScalarTower R S F` this proof must build for a residue
field `F` typechecks on the nose. At the concrete localization it would instead have to reconcile
`Algebra.toSMul` with `OreLocalization.instSMulOfIsScalarTower` — the same class of instance
diamond that made the earlier, localization-first version of this proof intractable. -/
theorem QuadraticForm.IsGPRNonsingular.bijective_baseChange_of_isLocalRing [Module.Finite R M]
    [Module.Projective R M] [Invertible (2 : R)] {Q : QuadraticForm R M}
    (hNS : Q.IsGPRNonsingular.{u, v, u}) (S : Type u) [CommRing S] [Algebra R S]
    [IsLocalRing S] :
    Function.Bijective (LinearMap.baseChange S
      (QuadraticMap.polarBilin Q : M →ₗ[R] Module.Dual R M)) := by
  set f : M →ₗ[R] Module.Dual R M := QuadraticMap.polarBilin Q with hf
  have : Module.Flat R M := Module.Flat.of_projective
  have : Module.Finite S (S ⊗[R] M) := Module.Finite.base_change R S M
  have : Module.Free S (S ⊗[R] M) := Module.free_of_flat_of_isLocalRing
  set v : Module.Basis (Module.Free.ChooseBasisIndex S (S ⊗[R] M)) S (S ⊗[R] M) :=
    Module.Free.chooseBasis S (S ⊗[R] M) with hv
  set g : (S ⊗[R] M) →ₗ[S] Module.Dual S (S ⊗[R] M) :=
    (Module.Dual.baseChangeEquivOfProjective (R := R) (M := M) (A := S)).toLinearMap ∘ₗ
      LinearMap.baseChange S f with hg
  suffices hgbij : Function.Bijective g by
    exact (Function.Bijective.of_comp_iff'
      (Module.Dual.baseChangeEquivOfProjective (R := R) (M := M) (A := S)).bijective
      (LinearMap.baseChange S f)).mp hgbij
  apply Module.Dual.bijective_of_forall_residue_field_injective v (g := g)
  -- `F` is an arbitrary residue field of `S`. Neither `𝔫` nor the kernel condition is used: all
  -- that matters is that `F` is a field with an `R`-algebra structure, which it acquires from
  -- `R → S → F`, since that is the only thing `hNS` asks of a base change.
  intro 𝔫 _ F _ _ _
  let : Algebra R F := ((algebraMap S F).comp (algebraMap R S)).toAlgebra
  have : IsScalarTower R S F := IsScalarTower.of_algebraMap_eq' rfl
  have : Invertible (2 : F) :=
    (Invertible.map (algebraMap R F) (2 : R)).copy 2 (map_ofNat (algebraMap R F) 2).symm
  have hE : Function.Injective (LinearMap.baseChange F
      (Module.Dual.baseChangeEquivOfProjective (R := R) (M := M) (A := S)).toLinearMap) := by
    rw [← LinearEquiv.coe_baseChange]
    exact LinearEquiv.injective _
  rw [hg, LinearMap.baseChange_comp]
  simp only [LinearMap.coe_comp]
  exact hE.comp hNS.injective_baseChange_baseChange

/-- For a fixed maximal ideal `𝔪`, `polarBilin Q` becomes bijective after base change to
`Localization.AtPrime 𝔪`. Immediate from `bijective_baseChange_of_isLocalRing`, since a
localization at a prime is local. -/
theorem QuadraticForm.IsGPRNonsingular.bijective_baseChange_atPrime [Module.Finite R M]
    [Module.Projective R M] [Invertible (2 : R)] {Q : QuadraticForm R M}
    (hNS : Q.IsGPRNonsingular.{u, v, u}) (𝔪 : Ideal R) [𝔪.IsMaximal] :
    Function.Bijective (LinearMap.baseChange (Localization.AtPrime 𝔪)
      (QuadraticMap.polarBilin Q : M →ₗ[R] Module.Dual R M)) :=
  hNS.bijective_baseChange_of_isLocalRing (Localization.AtPrime 𝔪)

/-- **`GN (C.8.2)`, converse direction.** `Q` non-singular implies `Q` regular, when `2 ∈ Rˣ`:
bundle `bijective_baseChange_atPrime` over every maximal ideal via
`LinearMap.bijective_of_forall_baseChange_atPrime_bijective`. -/
theorem QuadraticForm.IsGPRNonsingular.isGPRRegular [Module.Finite R M] [Module.Projective R M]
    [Invertible (2 : R)] {Q : QuadraticForm R M} (hNS : Q.IsGPRNonsingular.{u, v, u}) :
    Q.IsGPRRegular :=
  LinearMap.bijective_of_forall_baseChange_atPrime_bijective (QuadraticMap.polarBilin Q)
    (fun 𝔪 _ ↦ hNS.bijective_baseChange_atPrime 𝔪)

/-- `GN (C.8.2)`, in full: for `M` finitely generated projective and `2 ∈ Rˣ`, `Q` is regular iff
`Q` is non-singular. Combines `QuadraticForm.IsGPRRegular.isGPRNonsingular` (no hypothesis on `2`
needed) with `QuadraticForm.IsGPRNonsingular.isGPRRegular` (the converse, needing `2 ∈ Rˣ`). -/
theorem QuadraticForm.isGPRRegular_iff_isGPRNonsingular [Module.Finite R M]
    [Module.Projective R M] [Invertible (2 : R)] (Q : QuadraticForm R M) :
    Q.IsGPRRegular ↔ Q.IsGPRNonsingular.{u, v, u} :=
  ⟨QuadraticForm.IsGPRRegular.isGPRNonsingular, QuadraticForm.IsGPRNonsingular.isGPRRegular⟩

/-! ### The rank-one form `⟨u⟩`, and the sharpness of `2 ∈ Rˣ`

`GN (C.8.1)` says regular implies non-singular unconditionally; `GN (C.8.2)` says the converse
holds when `2 ∈ Rˣ`. The rank-one form `⟨u⟩ : r ↦ u * r ^ 2` shows that hypothesis cannot be
dropped: for `u` a unit, `⟨u⟩` is non-singular over any commutative ring but regular exactly when
`2` is a unit. `R = ℤ`, `u = 1` is the concrete separating example.

The two directions use genuinely different features of the definitions. Non-singularity needs only
the `Q m = 0` clause of `QuadraticMap.radical` — the clause that makes the radical smaller than the
kernel of the polar form, which is all that mathlib's `LinearMap.BilinForm.Nondegenerate` sees —
together with the absence of zero divisors in a field. Regularity, by contrast, is entirely about
the polar form `x ↦ 2 * u * x`, which is where the `2` enters.
-/

/-- The **rank-one form** `⟨u⟩ : r ↦ u * r ^ 2` on `R` itself.

This is mathlib's `QuadraticMap.sq` scaled by `u`, not a new construction; the abbreviation exists
only so that `GPR`'s `⟨u⟩` has a name here. -/
def QuadraticForm.rankOne (u : R) : QuadraticForm R R := u • QuadraticMap.sq

@[simp]
theorem QuadraticForm.rankOne_apply (u r : R) : QuadraticForm.rankOne u r = u * r ^ 2 := by
  simp [QuadraticForm.rankOne, QuadraticMap.sq, pow_two]

/-- The polar form of `⟨u⟩` is `(x, y) ↦ 2 * u * x * y`: the factor `2` that `GN (C.8.2)` must
invert is visible here, and is the whole content of the example. -/
@[simp]
theorem QuadraticForm.polar_rankOne (u x y : R) :
    QuadraticMap.polar (QuadraticForm.rankOne u) x y = 2 * u * (x * y) := by
  simp only [QuadraticMap.polar, QuadraticForm.rankOne_apply]
  ring

/-- The same computation for `polarBilin`. Not a `simp` lemma: `simp` already reaches this via
`QuadraticMap.polarBilin_apply_apply` and `QuadraticForm.polar_rankOne`. -/
theorem QuadraticForm.polarBilin_rankOne_apply_apply (u x y : R) :
    QuadraticMap.polarBilin (QuadraticForm.rankOne u) x y = 2 * u * (x * y) :=
  (QuadraticMap.polarBilin_apply_apply _ _ _).trans (QuadraticForm.polar_rankOne u x y)

/-- `⟨u⟩` is regular exactly when `2 * u` is a unit. Under `Module.Dual R R ≅ R` the polar form is
multiplication by `2 * u`; surjectivity forces `2 * u * x = 1` for some `x`, and conversely an
inverse `w` of `2 * u` builds both the injectivity witness and the preimage `w * f 1` of an
arbitrary functional `f`. -/
theorem QuadraticForm.isGPRRegular_rankOne_iff (u : R) :
    (QuadraticForm.rankOne u).IsGPRRegular ↔ IsUnit (2 * u) := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := h.surjective (LinearMap.id : Module.Dual R R)
    have h1 : 2 * u * (x * 1) = 1 := by
      simpa only [QuadraticForm.polarBilin_rankOne_apply_apply, LinearMap.id_coe, id_eq]
        using DFunLike.congr_fun hx (1 : R)
    exact IsUnit.of_mul_eq_one x (by rw [← h1]; ring)
  · intro hu
    obtain ⟨w, hw⟩ := hu.exists_right_inv
    constructor
    · rw [injective_iff_map_eq_zero]
      intro x hx
      have h1 : 2 * u * (x * 1) = 0 := by
        simpa only [QuadraticForm.polarBilin_rankOne_apply_apply, LinearMap.zero_apply]
          using DFunLike.congr_fun hx (1 : R)
      calc x = 2 * u * w * x := by rw [hw, one_mul]
        _ = w * (2 * u * (x * 1)) := by ring
        _ = 0 := by rw [h1, mul_zero]
    · intro f
      refine ⟨w * f 1, LinearMap.ext fun y ↦ ?_⟩
      have hfy : f y = y * f 1 := by
        conv_lhs => rw [← mul_one y, ← smul_eq_mul, map_smul]
        rw [smul_eq_mul]
      rw [QuadraticForm.polarBilin_rankOne_apply_apply, hfy]
      calc 2 * u * (w * f 1 * y) = 2 * u * w * (y * f 1) := by ring
        _ = y * f 1 := by rw [hw, one_mul]

/-- For `u` a unit, `⟨u⟩` is regular exactly when `2 ∈ Rˣ`. -/
theorem QuadraticForm.isGPRRegular_rankOne_iff_isUnit_two {u : R} (hu : IsUnit u) :
    (QuadraticForm.rankOne u).IsGPRRegular ↔ IsUnit (2 : R) := by
  rw [QuadraticForm.isGPRRegular_rankOne_iff, (Commute.all (2 : R) u).isUnit_mul_iff]
  exact and_iff_left hu

/-- For `u` a unit, `⟨u⟩` is non-singular over *every* base ring, with no hypothesis on `2`.

Every element of `F ⊗[R] R` is `a ⊗ₜ 1`, on which the base-changed form takes the value
`u • (a * a)`. The image of `u` in `F` is a unit, so `u • (a * a) = 0` forces `a * a = 0`, hence
`a = 0` since a field has no zero divisors. Only the `Q m = 0` half of `QuadraticMap.radical` is
used;
the polar form never enters, which is exactly why no assumption on `2` is needed. -/
theorem QuadraticForm.isGPRNonsingular_rankOne {u : R} (hu : IsUnit u) :
    (QuadraticForm.rankOne u).IsGPRNonsingular := by
  intro F _ _
  refine (((QuadraticForm.rankOne u).baseChangeOfProjective F).radical.eq_bot_iff).mpr
    fun x hx ↦ ?_
  obtain ⟨a, rfl⟩ : ∃ a : F, x = a ⊗ₜ[R] (1 : R) :=
    ⟨TensorProduct.rid R F x, by
      conv_lhs => rw [← (TensorProduct.rid R F).symm_apply_apply x]
      rw [TensorProduct.rid_symm_apply]⟩
  have hQ := hx.1
  rw [QuadraticForm.baseChangeOfProjective_tmul, QuadraticForm.rankOne_apply, one_pow, mul_one,
    Algebra.smul_def] at hQ
  have ha : a = 0 :=
    mul_self_eq_zero.mp ((hu.map (algebraMap R F)).mul_right_eq_zero.mp hQ)
  rw [ha, TensorProduct.zero_tmul]

/-- **The separating example, half one.** Over `ℤ`, the form `⟨1⟩ : r ↦ r ^ 2` is non-singular.
Paired with `QuadraticForm.not_isGPRRegular_rankOne_one_int`, this shows `IsGPRNonsingular` is
strictly weaker than `IsGPRRegular` over a general commutative ring. -/
theorem QuadraticForm.isGPRNonsingular_rankOne_one_int :
    (QuadraticForm.rankOne (1 : ℤ)).IsGPRNonsingular :=
  QuadraticForm.isGPRNonsingular_rankOne isUnit_one

/-- **The separating example, half two.** Over `ℤ`, the form `⟨1⟩ : r ↦ r ^ 2` is *not* regular,
since `2` is not a unit in `ℤ`. So the hypothesis `[Invertible (2 : R)]` in
`QuadraticForm.isGPRRegular_iff_isGPRNonsingular` is not removable. -/
theorem QuadraticForm.not_isGPRRegular_rankOne_one_int :
    ¬ (QuadraticForm.rankOne (1 : ℤ)).IsGPRRegular := by
  rw [QuadraticForm.isGPRRegular_rankOne_iff]
  simp [Int.isUnit_iff]

/-! ### Rescaling by a unit

Multiplying a quadratic form by a unit changes neither its radical nor any of the rungs of the
ladder. This is the `⟨-μ⟩ q` of the Cayley–Dickson norm `q ⊥ ⟨-μ⟩ q`, where `μ` is a unit exactly
in the theorems that need the double to be a composition algebra. -/

/-- Rescaling by a unit does not change the radical: `c * Q m = 0 ↔ Q m = 0` and likewise for the
polar form. -/
theorem QuadraticMap.radical_smul_of_isUnit {c : R} (hc : IsUnit c) (Q : QuadraticForm R M) :
    (c • Q).radical = Q.radical := by
  have key : ∀ a : R, c * a = 0 ↔ a = 0 := fun a ↦ hc.mul_right_eq_zero
  have hpolar : ∀ x y : M, QuadraticMap.polar (c • Q) x y = c * QuadraticMap.polar Q x y := by
    intro x y
    simp only [QuadraticMap.polar, smul_apply, smul_eq_mul]
    ring
  ext x
  simp only [QuadraticMap.radical, Submodule.mem_mk, AddSubmonoid.mem_mk,
    AddSubsemigroup.mem_mk, Set.mem_ofPred_eq, smul_apply, smul_eq_mul,
    LinearMap.ext_iff, QuadraticMap.polarBilin_apply_apply, LinearMap.zero_apply]
  exact and_congr (key _) (forall_congr' fun y ↦ by rw [hpolar, key])

/-- Rescaling by a unit preserves non-singularity, since it does so after every base change: the
image of a unit under `algebraMap` is a unit. -/
theorem QuadraticForm.IsGPRNonsingular.smul_of_isUnit [Module.Finite R M] [Module.Projective R M]
    {c : R} (hc : IsUnit c) {Q : QuadraticForm R M} (h : Q.IsGPRNonsingular.{u, v, w}) :
    QuadraticForm.IsGPRNonsingular.{u, v, w} (c • Q) := by
  intro F _ _
  rw [QuadraticForm.baseChangeOfProjective_smul,
    QuadraticMap.radical_smul_of_isUnit (hc.map (algebraMap R F))]
  exact h F

/-! ### `GN (C.8.3)`: orthogonal sums

`GN C.8(f)` records how the ladder behaves under the orthogonal sum `q₁ ⊥ q₂` — mathlib's
`QuadraticMap.prod`. Regularity is symmetric (`q₁ ⊥ q₂` is regular iff both are), but
non-singularity is not, and `(C.8.3)` is exactly the pair of implications that do hold:

  `q₁ ⊥ q₂` non-singular ⇒ `q₁` and `q₂` non-singular,
  `q₁` **regular** and `q₂` non-singular ⇒ `q₁ ⊥ q₂` non-singular.

The asymmetry is real, and visible in the radical: `rad (q₁ ⊥ q₂)` contains `rad q₁ × rad q₂` but
can be strictly larger, because `q₁ m₁ + q₂ m₂ = 0` does not force `q₁ m₁ = 0 = q₂ m₂`. Regularity
of `q₁` is what kills the first coordinate outright and lets the second-coordinate equation
collapse. -/

section OrthogonalSum

variable {M₁ : Type*} [AddCommGroup M₁] [Module R M₁]
  {M₂ : Type*} [AddCommGroup M₂] [Module R M₂]

/-- `(x, 0)` lies in the radical of `Q₁ ⊥ Q₂` when `x` lies in the radical of `Q₁`. -/
theorem QuadraticMap.inl_mem_radical_prod {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
    {x : M₁} (hx : x ∈ Q₁.radical) : (x, (0 : M₂)) ∈ (Q₁.prod Q₂).radical := by
  refine ⟨by simp [QuadraticMap.prod_apply, hx.1], LinearMap.ext fun y ↦ ?_⟩
  have h1 : QuadraticMap.polar Q₁ x y.1 = 0 := by
    have h := DFunLike.congr_fun hx.2 y.1
    rwa [QuadraticMap.polarBilin_apply_apply, LinearMap.zero_apply] at h
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_prod, h1,
    QuadraticMap.polar_zero_left, add_zero, LinearMap.zero_apply]

/-- `(0, x)` lies in the radical of `Q₁ ⊥ Q₂` when `x` lies in the radical of `Q₂`. -/
theorem QuadraticMap.inr_mem_radical_prod
    {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
    {x : M₂} (hx : x ∈ Q₂.radical) : ((0 : M₁), x) ∈ (Q₁.prod Q₂).radical := by
  refine ⟨by simp [QuadraticMap.prod_apply, hx.1], LinearMap.ext fun y ↦ ?_⟩
  have h1 : QuadraticMap.polar Q₂ x y.2 = 0 := by
    have h := DFunLike.congr_fun hx.2 y.2
    rwa [QuadraticMap.polarBilin_apply_apply, LinearMap.zero_apply] at h
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_prod, h1,
    QuadraticMap.polar_zero_left, zero_add, LinearMap.zero_apply]

/-- A vanishing radical passes to the left summand. -/
theorem QuadraticMap.radical_eq_bot_left_of_radical_prod_eq_bot {Q₁ : QuadraticForm R M₁}
    {Q₂ : QuadraticForm R M₂} (h : (Q₁.prod Q₂).radical = ⊥) : Q₁.radical = ⊥ := by
  refine (Q₁.radical).eq_bot_iff.mpr fun x hx ↦ ?_
  have hmem := QuadraticMap.inl_mem_radical_prod (Q₂ := Q₂) hx
  rw [h, Submodule.mem_bot, Prod.mk_eq_zero] at hmem
  exact hmem.1

/-- A vanishing radical passes to the right summand. -/
theorem QuadraticMap.radical_eq_bot_right_of_radical_prod_eq_bot {Q₁ : QuadraticForm R M₁}
    {Q₂ : QuadraticForm R M₂} (h : (Q₁.prod Q₂).radical = ⊥) : Q₂.radical = ⊥ := by
  refine (Q₂.radical).eq_bot_iff.mpr fun x hx ↦ ?_
  have hmem := QuadraticMap.inr_mem_radical_prod (Q₁ := Q₁) hx
  rw [h, Submodule.mem_bot, Prod.mk_eq_zero] at hmem
  exact hmem.2

/-- The ring-level heart of `GN (C.8.3)`: an *injective* polar form on the left summand plus a
vanishing radical on the right gives a vanishing radical on the sum.

Injectivity on the left is what breaks the symmetry. It forces the first coordinate of a radical
vector to vanish, after which `Q₁ 0 + Q₂ x₂ = 0` really does say `Q₂ x₂ = 0`. -/
theorem QuadraticMap.radical_prod_eq_bot {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
    (h₁ : Function.Injective (QuadraticMap.polarBilin Q₁)) (h₂ : Q₂.radical = ⊥) :
    (Q₁.prod Q₂).radical = ⊥ := by
  refine ((Q₁.prod Q₂).radical).eq_bot_iff.mpr fun x hx ↦ ?_
  have hp1 : QuadraticMap.polarBilin Q₁ x.1 = 0 := LinearMap.ext fun y₁ ↦ by
    have h := DFunLike.congr_fun hx.2 (y₁, (0 : M₂))
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_prod, LinearMap.zero_apply,
      QuadraticMap.polar_zero_right, add_zero] at h
    rw [QuadraticMap.polarBilin_apply_apply, h, LinearMap.zero_apply]
  have hx1 : x.1 = 0 := (injective_iff_map_eq_zero _).mp h₁ _ hp1
  have hp2 : QuadraticMap.polarBilin Q₂ x.2 = 0 := LinearMap.ext fun y₂ ↦ by
    have h := DFunLike.congr_fun hx.2 ((0 : M₁), y₂)
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_prod, LinearMap.zero_apply,
      QuadraticMap.polar_zero_right, zero_add] at h
    rw [QuadraticMap.polarBilin_apply_apply, h, LinearMap.zero_apply]
  have hQ2 : Q₂ x.2 = 0 := by
    have h := hx.1
    rwa [QuadraticMap.prod_apply, hx1, QuadraticMap.map_zero, zero_add] at h
  have hmem : x.2 ∈ Q₂.radical := ⟨hQ2, hp2⟩
  rw [h₂, Submodule.mem_bot] at hmem
  exact Prod.ext hx1 hmem

/-- The polar form of a precomposition is the precomposed polar form: the pointwise form of
mathlib's `QuadraticMap.polarBilin_comp`. -/
theorem QuadraticMap.polar_comp_apply {M' : Type*} [AddCommGroup M'] [Module R M']
    (Q : QuadraticMap R M N) (f : M' →ₗ[R] M) (x y : M') :
    QuadraticMap.polar (Q.comp f) x y = QuadraticMap.polar Q (f x) (f y) := by
  simpa using LinearMap.congr_fun₂ (Q.polarBilin_comp f) x y

/-- Radical membership transports along a linear equivalence: mathlib's
`QuadraticMap.IsometryEquiv.map_radical` for the isometry `Q ≅ Q ∘ e`. -/
theorem QuadraticMap.mem_radical_comp_linearEquiv {M' : Type*} [AddCommGroup M'] [Module R M']
    (Q : QuadraticMap R M N) (e : M' ≃ₗ[R] M) {x : M'} :
    x ∈ (Q.comp e.toLinearMap).radical ↔ e x ∈ Q.radical := by
  rw [← (Q.isometryEquivOfCompLinearEquiv e).map_radical]
  exact Submodule.mem_map_equiv (e := (Q.isometryEquivOfCompLinearEquiv e).toLinearEquiv) _

/-- Transporting a vanishing radical along a linear equivalence. -/
theorem QuadraticMap.radical_comp_linearEquiv_eq_bot_iff {M' : Type*} [AddCommGroup M']
    [Module R M'] (Q : QuadraticMap R M N) (e : M' ≃ₗ[R] M) :
    (Q.comp e.toLinearMap).radical = ⊥ ↔ Q.radical = ⊥ := by
  rw [← (Q.isometryEquivOfCompLinearEquiv e).map_radical]
  exact Submodule.map_eq_bot_iff (e := (Q.isometryEquivOfCompLinearEquiv e).toLinearEquiv)

/-- **Base change of an orthogonal sum is the orthogonal sum of the base changes**, along the
canonical `A ⊗[R] (M₁ × M₂) ≃ (A ⊗[R] M₁) × (A ⊗[R] M₂)`. Checked on pure tensors `1 ⊗ₜ m`,
where both sides come down to `add_smul`. -/
theorem QuadraticForm.baseChangeOfProjective_prod {A : Type*} [CommRing A] [Algebra R A]
    [Module.Finite R M₁] [Module.Projective R M₁]
    [Module.Finite R M₂] [Module.Projective R M₂]
    (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) :
    QuadraticForm.baseChangeOfProjective A (Q₁.prod Q₂) =
      ((Q₁.baseChangeOfProjective A).prod (Q₂.baseChangeOfProjective A)).comp
        (TensorProduct.prodRight R A A M₁ M₂).toLinearMap := by
  refine baseChange_ext fun m ↦ ?_
  simp only [QuadraticForm.baseChangeOfProjective_tmul, QuadraticMap.comp_apply,
    LinearEquiv.coe_coe, TensorProduct.prodRight_tmul, QuadraticMap.prod_apply]
  rw [add_smul]

end OrthogonalSum

section TransportNonsingular

/-- **Regularity transports along a linear equivalence.**

The polar map of `Q ∘ e` factors as `e* ∘ polarBilin Q ∘ e`, a composition of three bijections;
no finiteness, projectivity or hypothesis on `2` is involved, unlike the non-singular version
below, which has to pass through base change. -/
theorem QuadraticForm.IsGPRRegular.comp_linearEquiv {M' : Type t₁} [AddCommGroup M'] [Module R M']
    {Q : QuadraticForm R M} (h : Q.IsGPRRegular) (e : M' ≃ₗ[R] M) :
    QuadraticForm.IsGPRRegular (Q.comp e.toLinearMap) := by
  have hfactor : (QuadraticMap.polarBilin (Q.comp e.toLinearMap) :
      M' →ₗ[R] Module.Dual R M') =
      (e.dualMap.toLinearMap ∘ₗ
          (QuadraticMap.polarBilin Q : M →ₗ[R] Module.Dual R M)) ∘ₗ e.toLinearMap := by
    refine LinearMap.ext fun x ↦ LinearMap.ext fun y ↦ ?_
    simp [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, QuadraticMap.comp_apply]
  rw [QuadraticForm.IsGPRRegular, hfactor]
  exact (e.dualMap.bijective.comp h).comp e.bijective

/-- Regularity is *equivalent* to regularity after precomposition with an equivalence. -/
theorem QuadraticForm.isGPRRegular_comp_linearEquiv_iff {M' : Type t₁} [AddCommGroup M']
    [Module R M'] {Q : QuadraticForm R M} (e : M' ≃ₗ[R] M) :
    QuadraticForm.IsGPRRegular (Q.comp e.toLinearMap) ↔ Q.IsGPRRegular := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.comp_linearEquiv e⟩
  have h2 := QuadraticForm.IsGPRRegular.comp_linearEquiv h e.symm
  rwa [show (Q.comp e.toLinearMap).comp e.symm.toLinearMap = Q from
    QuadraticMap.ext fun x ↦ by simp] at h2

/-- **Non-singularity transports along a linear equivalence.**

Base change turns the equivalence `e : M' ≃ M` into an equivalence `F ⊗ M' ≃ F ⊗ M`
(`LinearEquiv.baseChange`), and a vanishing radical is invariant under precomposition with an
equivalence (`QuadraticMap.radical_comp_linearEquiv_eq_bot_iff`). -/
theorem QuadraticForm.IsGPRNonsingular.comp_linearEquiv [Module.Finite R M]
    [Module.Projective R M] {M' : Type t₁} [AddCommGroup M'] [Module R M'] [Module.Finite R M']
    [Module.Projective R M'] {Q : QuadraticForm R M}
    (h : QuadraticForm.IsGPRNonsingular.{u, v, t₃} Q) (e : M' ≃ₗ[R] M) :
    QuadraticForm.IsGPRNonsingular.{u, t₁, t₃} (Q.comp e.toLinearMap) := by
  intro F _ _
  rw [QuadraticForm.baseChangeOfProjective_comp,
    show LinearMap.baseChange F e.toLinearMap = (e.baseChange R F M' M).toLinearMap from rfl,
    QuadraticMap.radical_comp_linearEquiv_eq_bot_iff]
  exact h F

end TransportNonsingular

section OrthogonalSumNonsingular

variable {M₁ : Type t₁} [AddCommGroup M₁] [Module R M₁] [Module.Finite R M₁]
  [Module.Projective R M₁]
  {M₂ : Type t₂} [AddCommGroup M₂] [Module R M₂] [Module.Finite R M₂]
  [Module.Projective R M₂]

/-- **`GN (C.8.3)`, first implication (left summand).** If `q₁ ⊥ q₂` is non-singular, so is `q₁`.

Over any field, a radical vector of `(q₁)_F` gives the radical vector `(x, 0)` of `(q₁ ⊥ q₂)_F`. -/
theorem QuadraticForm.IsGPRNonsingular.of_prod_left {Q₁ : QuadraticForm R M₁}
    {Q₂ : QuadraticForm R M₂}
    (h : QuadraticForm.IsGPRNonsingular.{u, max t₁ t₂, t₃} (Q₁.prod Q₂)) :
    QuadraticForm.IsGPRNonsingular.{u, t₁, t₃} Q₁ := by
  intro F _ _
  have hF := h F
  rw [QuadraticForm.baseChangeOfProjective_prod,
    QuadraticMap.radical_comp_linearEquiv_eq_bot_iff] at hF
  exact QuadraticMap.radical_eq_bot_left_of_radical_prod_eq_bot hF

/-- **`GN (C.8.3)`, first implication (right summand).** If `q₁ ⊥ q₂` is non-singular, so is
`q₂`. -/
theorem QuadraticForm.IsGPRNonsingular.of_prod_right {Q₁ : QuadraticForm R M₁}
    {Q₂ : QuadraticForm R M₂}
    (h : QuadraticForm.IsGPRNonsingular.{u, max t₁ t₂, t₃} (Q₁.prod Q₂)) :
    QuadraticForm.IsGPRNonsingular.{u, t₂, t₃} Q₂ := by
  intro F _ _
  have hF := h F
  rw [QuadraticForm.baseChangeOfProjective_prod,
    QuadraticMap.radical_comp_linearEquiv_eq_bot_iff] at hF
  exact QuadraticMap.radical_eq_bot_right_of_radical_prod_eq_bot hF

/-- **`GN (C.8.3)`, second implication.** `q₁` **regular** and `q₂` non-singular imply `q₁ ⊥ q₂`
non-singular.

Regularity of `q₁` — not merely non-singularity — is what is needed: it survives base change as
*injectivity* of the polar form (`IsGPRRegular.injective_polarBilin_baseChangeOfProjective`), and
that is exactly the hypothesis `QuadraticMap.radical_prod_eq_bot` consumes.

The hypothesis cannot be weakened to "`q₁` non-singular". Over a field of characteristic `2` the
polar form of `⟨1⟩` vanishes identically, so `⟨1⟩` is non-singular (`isGPRNonsingular_rankOne`)
purely because `a ^ 2 = 0` forces `a = 0`; but `⟨1⟩ ⊥ ⟨1⟩` sends `(a, b)` to
`a ^ 2 + b ^ 2 = (a + b) ^ 2`, whose zero set is the line `a = b`, so the sum has a nonzero
radical. That counterexample is not formalized here. -/
theorem QuadraticForm.IsGPRRegular.prod_isGPRNonsingular {Q₁ : QuadraticForm R M₁}
    {Q₂ : QuadraticForm R M₂} (h₁ : Q₁.IsGPRRegular)
    (h₂ : QuadraticForm.IsGPRNonsingular.{u, t₂, t₃} Q₂) :
    QuadraticForm.IsGPRNonsingular.{u, max t₁ t₂, t₃} (Q₁.prod Q₂) := by
  intro F _ _
  rw [QuadraticForm.baseChangeOfProjective_prod, QuadraticMap.radical_comp_linearEquiv_eq_bot_iff]
  exact QuadraticMap.radical_prod_eq_bot
    (h₁.injective_polarBilin_baseChangeOfProjective F) (h₂ F)

end OrthogonalSumNonsingular

/-- `Q` is **non-degenerate** in `EKM`'s sense (`EKM Definition 7.17`, condition (1) of
`Lemma 7.16`): unlike every other predicate in this file, this is only meaningful for `Q` over a
*field* `R` — `EKM` never considers quadratic forms over a general commutative ring, so there is
no ring-level analogue to state here. `Q` is `IsEKMNondegenerate` when its radical vanishes after
base change along *every* field extension `K` of `R`.

**Terminology.** Named for its source, `EKM`, since `EKM`'s "non-degenerate" is a different,
stronger condition than `GPR`'s "non-degenerate" — see `QuadraticForm.IsGPRNondegenerate` above.
`EKM`'s own weaker condition, `radical Q = ⊥`, is what `EKM` calls "regular", and is *not* what this
predicate captures — that is `QuadraticForm.IsGPRNondegenerate`, again via the naming clash noted
there. -/
def QuadraticForm.IsEKMNondegenerate.{w2} {F : Type u} [Field F] {V : Type v}
    [AddCommGroup V] [Module F V] [Module.Finite F V] [Module.Projective F V]
    (Q : QuadraticForm F V) : Prop :=
  QuadraticForm.IsGPRNonsingular.{u, v, w2} Q

/-- Over a field `R`, `EKM`'s non-degenerate (`QuadraticForm.IsEKMNondegenerate`) is *literally*
the same universal statement as `GPR`'s non-singular (`QuadraticForm.IsGPRNonsingular`): both
quantify `(Q.baseChangeOfProjective K).radical = ⊥` over the same class of fields `K` with
`[Algebra R K]`. `EKM Lemma 7.16` itself — that this condition agrees with `EKM`'s other two
formulations — is `QuadraticForm.isEKMNondegenerate_iff_nondegenerate`, in
`QuadraticForm/NonsingularOverFields.lean`; this theorem only records that the definition chosen
here for `IsEKMNondegenerate` (condition (1) of the lemma) coincides on the nose with the
ring-theoretic `IsGPRNonsingular` once the ring is a field, which is `GN C.9`'s claim. -/
theorem QuadraticForm.isEKMNondegenerate_iff_isGPRNonsingular.{w2} {F : Type u} [Field F]
    {V : Type v} [AddCommGroup V] [Module F V] [Module.Finite F V] [Module.Projective F V]
    (Q : QuadraticForm F V) :
    QuadraticForm.IsEKMNondegenerate.{u, v, w2} Q ↔ QuadraticForm.IsGPRNonsingular.{u, v, w2} Q :=
  Iff.rfl
