/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
import CompositionAlgebras.Composition.Examples
import CompositionAlgebras.Composition.RankOneTwoFourEight

/-!
# The sedenions: a conic algebra that is not a composition algebra (`GPR 19.23`)

The fourth rung of the Cayley–Dickson tower, `Cay(𝕆, μ)` of rank `16`, is a conic algebra — the
doubling construction has no hypotheses at all — but it is not a composition algebra. This is the
example that shows the tower really does stop, rather than merely resisting the theorems that
built it.

Three separate statements are proved, in increasing strength:

* the sedenions are **not alternative**, the converse half of `GPR 18.14(c)` applied to the
  non-associativity of `𝕆`;
* their norm is **non-singular but not multiplicative** — so the failure is in the composition law
  itself, not in a degeneracy of the norm;
* **no** conic structure on a sixteen-dimensional space is a composition algebra, by the rank
  dichotomy `GPR 19.18`. This last one does not look at the multiplication at all.

## Two independent routes

The first two statements go through alternativity: `𝕆` is not associative
(`ConicAlgebra.exists_mul_mul_ne_mul_mul_realOctonion`), so `Cay(𝕆, μ)` is not alternative
(`ConicAlgebra.not_isAlternative_cay_of_mul_mul_ne`), and over a field every composition algebra is
alternative (`GPR 19.3`). This is the route `GPR` takes.

The third goes through the rank: `16 ∉ {1, 2, 4, 8}`. It is strictly stronger — it rules out every
conic norm on the underlying module at once, rather than the one that doubling produces — and it
needs no witness and no computation with associators.

That the norm is non-singular is what makes the second statement sharp. A conic algebra can fail to
be a composition algebra because its norm is degenerate (`GPR 19.4` in characteristic two is that
example, with an identically zero polar form); the sedenions fail for the opposite reason. Their
norm is the sixteen-fold orthogonal sum of `⟨1⟩` over `ℝ`, as non-singular as a form can be, and
what fails is `n(xy) = n(x)n(y)`. This is the converse half of `GPR Exc. 18.18` in this one
instance,
obtained without proving that converse in general.

## Main results

* `ConicAlgebra.RealSedenion`, `ConicAlgebra.realSedenion` : the algebra and its conic structure.
* `ConicAlgebra.not_isAlternative_realSedenion` : **not alternative**.
* `ConicAlgebra.not_isMultiplicative_realSedenion` : **the norm does not permit composition**.
* `ConicAlgebra.not_isComposition_conicAlgebra_realSedenion` : no conic structure on the sedenions
  is a composition algebra.
* `ConicAlgebra.IsComposition.not_cay_of_mul_mul_ne` : the general statement over a field, of which
  the sedenions are the instance.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 18.14(c),
  Exc. 18.18,
  19.3, 19.18, 19.23.
-/

universe u v

namespace ConicAlgebra

/-! ### The general statement over a field -/

section Field

variable {F : Type u} {B : Type v} [Field F] [NonAssocRing B] [Module F B]
  [SMulCommClass F B B] [IsScalarTower F B B] [Module.Finite F B] [Module.Projective F B]

/-- **The double of a non-associative conic algebra over a field is not a composition algebra.**

`ConicAlgebra.not_isAlternative_cay_of_mul_mul_ne` — the converse half of `GPR 18.14(c)` — says the
double is not alternative, and over a field every composition algebra is alternative
(`GPR 19.3`, `ConicAlgebra.IsComposition.isAlternative`). No hypothesis on `μ`. -/
theorem IsComposition.not_cay_of_mul_mul_ne (C : ConicAlgebra F B) (μ : F) {a b c : B}
    (hne : a * b * c ≠ a * (b * c)) : ¬ (C.cay μ).IsComposition.{u, v, u} := fun h ↦
  not_isAlternative_cay_of_mul_mul_ne C μ hne h.isAlternative

end Field

/-! ### The sedenions over `ℝ` -/

/-- **The real sedenions**, `Cay(𝕆, -1)`: the fourth rung of the Cayley–Dickson tower over `ℝ`,
of dimension `16`. -/
abbrev RealSedenion : Type := Cay realOctonion (-1)

/-- The conic structure on the sedenions. Doubling needs no hypotheses, so this exists exactly as
the earlier rungs do; what fails is everything *after* `GPR 18.4`. -/
noncomputable abbrev realSedenion : ConicAlgebra ℝ RealSedenion := realOctonion.cay (-1)

/-- **The sedenions have dimension 16.** -/
theorem finrank_realSedenion : Module.finrank ℝ RealSedenion = 16 := by
  rw [Cay.finrank_cay, finrank_realOctonion]

/-- **The sedenions are not alternative.** `𝕆` is not associative, and by the converse half of
`GPR 18.14(c)` that is exactly the obstruction. -/
theorem not_isAlternative_realSedenion : ¬ IsAlternative RealSedenion :=
  let ⟨_, _, _, h⟩ := exists_mul_mul_ne_mul_mul_realOctonion
  not_isAlternative_cay_of_mul_mul_ne realOctonion (-1) h

/-- **The sedenion norm is non-singular.** It is `n_𝕆 ⊥ ⟨1⟩ n_𝕆`, and `GN (C.8.3)` builds
non-singularity of an orthogonal sum out of *regularity* of the first summand — which the octonion
norm has, since `2` is invertible in `ℝ`.

This is what makes `ConicAlgebra.not_isMultiplicative_realSedenion` sharp: the sedenions are not a
composition algebra because composition fails, not because the norm degenerates. -/
theorem isGPRNonsingular_realSedenion :
    QuadraticForm.IsGPRNonsingular.{0, 0, 0} realSedenion.norm := by
  let : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
  have hreg : realOctonion.norm.IsGPRRegular :=
    isComposition_realOctonion.isGPRNonsingular.isGPRRegular
  exact hreg.prod_isGPRNonsingular
    (hreg.isGPRNonsingular.smul_of_isUnit (by norm_num : IsUnit (-(-1 : ℝ))))

/-- **`GPR 19.23`.** The sedenion norm does not permit composition: `n(xy) = n(x)n(y)` fails.

Its norm is non-singular, so were it multiplicative the sedenions would be a composition algebra of
dimension `16`, which `GPR 19.18` forbids. This is the converse half of `GPR Exc. 18.18` in this
instance, obtained without proving that converse in general. -/
theorem not_isMultiplicative_realSedenion : ¬ realSedenion.IsMultiplicative := fun hmul ↦
  not_isComposition_of_finrank_notMem realSedenion
    (by rw [finrank_realSedenion]; norm_num) (by rw [finrank_realSedenion]; norm_num)
    (by rw [finrank_realSedenion]; norm_num) (by rw [finrank_realSedenion]; norm_num)
    ⟨isGPRNonsingular_realSedenion, hmul⟩

/-- **The sedenions are not a composition algebra**, for the conic structure the Cayley–Dickson
process gives them. -/
theorem not_isComposition_realSedenion : ¬ realSedenion.IsComposition.{0, 0, 0} := fun h ↦
  not_isMultiplicative_realSedenion h.isMultiplicative

/-- **No conic structure on the sedenions is a composition algebra.** The rank dichotomy
`GPR 19.18` rules out dimension `16` outright, for every choice of conic norm at once — this looks
at the underlying module only, never at the multiplication. -/
theorem not_isComposition_conicAlgebra_realSedenion (C : ConicAlgebra ℝ RealSedenion) :
    ¬ C.IsComposition.{0, 0, 0} :=
  not_isComposition_of_finrank_notMem C
    (by rw [finrank_realSedenion]; norm_num) (by rw [finrank_realSedenion]; norm_num)
    (by rw [finrank_realSedenion]; norm_num) (by rw [finrank_realSedenion]; norm_num)

end ConicAlgebra
