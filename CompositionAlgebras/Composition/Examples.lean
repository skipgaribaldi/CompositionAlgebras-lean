/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
import CompositionAlgebras.Composition.Octonion
import Mathlib.Basic.Real.Basic

/-!
# The classical tower `ℝ, ℂ, ℍ, 𝕆`

Specializing the Cayley–Dickson tower of `Composition/Octonion.lean` to
`μ₁ = μ₂ = μ₃ = -1` over
an ordered field gives the classical chain of **division** composition algebras, of ranks
`1, 2, 4, 8`. Over `ℝ` these are the reals, the complex numbers, the quaternions and the
octonions.

The mechanism is that a negative scalar keeps the norm **positive definite**: the norm of
`Cay(B, μ)` is `n_B(u) - μ n_B(v)`, and for `μ < 0` that is a sum of two non-negative terms which
vanishes only when both do. A positive definite form is anisotropic, and an anisotropic
multiplicative norm makes the algebra a division algebra, because `x x̄ = n(x)·1` exhibits
`n(x)⁻¹ · x̄` as a two-sided inverse of `x`.

Note that division is obtained here **without** alternativity or associativity: the identity
`x x̄ = x̄ x = n(x)·1` holds in every conic algebra, so the inverse is immediate once `n(x)` is a
unit. Alternativity is
what makes the inverse well behaved (`GPR 19.x`), not what makes it exist.

## Main results

* `ConicAlgebra.PosDef.cay` : `μ < 0` preserves positive definiteness under doubling.
* `ConicAlgebra.exists_mul_eq_one_of_anisotropic` : an anisotropic conic algebra over a field is a
  division algebra.
* `ConicAlgebra.posDef_cay₈`, `ConicAlgebra.exists_inv_cay₈` : the rank-8 member of the tower at
  negative scalars is positive definite, hence a division algebra.
* `ConicAlgebra.RealOctonion` : the real octonions `𝕆`, with `finrank_realOctonion` (rank 8),
  `isComposition_realOctonion`, `isAlternative_realOctonion` and
  `exists_inv_realOctonion`.
* `ConicAlgebra.exists_mul_ne_mul_realQuaternion`,
  `ConicAlgebra.exists_mul_mul_ne_mul_mul_realOctonion` : `ℍ` is not commutative and `𝕆` is not
  associative — the explicit witnesses that the tower stops.

## Not done here

`ℂ` and `ℍ` are **not** identified with mathlib's `Complex` and `Quaternion ℝ`. Those
`AlgEquiv`s are a separate piece of work (they need explicit bases matched up), and nothing below
depends on them; see the README. What is proved here is that `ConicAlgebra.Cay₂ ℝ (-1)` and
`ConicAlgebra.Cay₄ ℝ (-1) (-1)` have all the structural properties the classical algebras have.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 19.18, 23.
-/

universe u v

namespace ConicAlgebra

/-! ### Positive definiteness under doubling -/

section Ordered

variable {k : Type u} [CommRing k] [LinearOrder k] [IsStrictOrderedRing k]
  {B : Type v} [NonAssocRing B] [Module k B] [SMulCommClass k B B] [IsScalarTower k B B]

/-- **Doubling at a negative scalar preserves positive definiteness.** The norm of `Cay(B, μ)` is
`n_B(u) - μ n_B(v)`; for `μ < 0` both terms are non-negative, and at least one is strictly
positive
unless `u = v = 0`. -/
theorem PosDef.cay (C : ConicAlgebra k B) {μ : k} (hμ : μ < 0) (h : C.norm.PosDef) :
    (C.cay μ).norm.PosDef := by
  intro x hx
  rw [cay_norm_apply]
  rcases eq_or_ne x.1 0 with h1 | h1
  · have h2 : x.2 ≠ 0 := fun h2 ↦ hx (Cay.ext h1 h2)
    have : 0 < -μ * C.norm x.2 := mul_pos (neg_pos.mpr hμ) (h _ h2)
    nlinarith [h.nonneg x.1]
  · nlinarith [h _ h1, h.nonneg x.2, neg_pos.mpr hμ]

variable (k) in
/-- The norm of the base ring, `x ↦ x²`, is positive definite. -/
theorem posDef_baseRing : (baseRing k).norm.PosDef := fun x hx ↦ by
  rw [baseRing_norm_apply]
  exact mul_self_pos.mpr hx

variable (k)

theorem posDef_cay₂ {μ₁ : k} (h₁ : μ₁ < 0) : (cay₂ k μ₁).norm.PosDef :=
  PosDef.cay _ h₁ (posDef_baseRing k)

theorem posDef_cay₄ {μ₁ μ₂ : k} (h₁ : μ₁ < 0) (h₂ : μ₂ < 0) :
    (cay₄ k μ₁ μ₂).norm.PosDef :=
  PosDef.cay _ h₂ (posDef_cay₂ k h₁)

/-- The rank-8 member of the tower at negative scalars has **positive definite** norm — over
`ℝ`, the sum of eight squares. -/
theorem posDef_cay₈ {μ₁ μ₂ μ₃ : k} (h₁ : μ₁ < 0) (h₂ : μ₂ < 0)
    (h₃ : μ₃ < 0) :
    (cay₈ k μ₁ μ₂ μ₃).norm.PosDef :=
  PosDef.cay _ h₃ (posDef_cay₄ k h₁ h₂)

end Ordered

/-! ### Anisotropic norms give division algebras -/

section Division

variable {K : Type u} [Field K] {A : Type v} [NonAssocRing A] [Module K A]
  [SMulCommClass K A A] [IsScalarTower K A A]

/-- **An anisotropic conic algebra over a field is a division algebra**: `n(x)⁻¹ • x̄` is a
two-sided inverse of any nonzero `x`.

Only `x x̄ = x̄ x = n(x)·1` is used, so this needs neither alternativity nor associativity nor
any
regularity of the norm beyond anisotropy. -/
theorem exists_mul_eq_one_of_anisotropic (C : ConicAlgebra K A) (hani : C.norm.Anisotropic)
    {x : A} (hx : x ≠ 0) :
    ∃ y : A, x * y = 1 ∧ y * x = 1 := by
  have hn : C.norm x ≠ 0 := fun h ↦ hx (hani x h)
  refine ⟨(C.norm x)⁻¹ • C.conj x, ?_, ?_⟩
  · rw [mul_smul_comm, C.mul_conj_self, smul_smul, inv_mul_cancel₀ hn, one_smul]
  · rw [smul_mul_assoc, C.conj_mul_self, smul_smul, inv_mul_cancel₀ hn, one_smul]

end Division

section OrderedField

variable (K : Type u) [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The rank-8 member of the tower at negative scalars over an ordered field is a **division
algebra**. -/
theorem exists_inv_cay₈ {μ₁ μ₂ μ₃ : K} (h₁ : μ₁ < 0) (h₂ : μ₂ < 0)
    (h₃ : μ₃ < 0)
    {x : Cay₈ K μ₁ μ₂ μ₃} (hx : x ≠ 0) : ∃ y, x * y = 1 ∧ y * x = 1 :=
  exists_mul_eq_one_of_anisotropic _ (posDef_cay₈ K h₁ h₂ h₃).anisotropic hx

end OrderedField

/-! ### The real octonions

⚠ `RealComplex` and `RealQuaternion` are the Cayley–Dickson doubles, not mathlib's `Complex` and
`Quaternion ℝ`; the identifying `AlgEquiv`s are not built here. -/

/-- `ℂ` as a Cayley–Dickson double, `Cay(ℝ, -1)`. -/
abbrev RealComplex : Type := Cay₂ ℝ (-1)

/-- `ℍ` as a Cayley–Dickson double, `Cay(ℂ, -1)`. -/
abbrev RealQuaternion : Type := Cay₄ ℝ (-1) (-1)

/-- **The real octonions `𝕆`**, `Cay(ℍ, -1)`. mathlib has no octonions; this is the
definition of
record here. -/
abbrev RealOctonion : Type := Cay₈ ℝ (-1) (-1) (-1)

/-- The conic structure on `𝕆`. -/
noncomputable abbrev realOctonion : ConicAlgebra ℝ RealOctonion := cay₈ ℝ (-1) (-1) (-1)

theorem finrank_realComplex : Module.finrank ℝ RealComplex = 2 := finrank_cay₂ ℝ _

theorem finrank_realQuaternion : Module.finrank ℝ RealQuaternion = 4 :=
  finrank_cay₄ ℝ _ _

/-- **`𝕆` has dimension 8 over `ℝ`.** -/
theorem finrank_realOctonion : Module.finrank ℝ RealOctonion = 8 :=
  finrank_cay₈ ℝ _ _ _

/-- **`𝕆` is alternative.** -/
theorem isAlternative_realOctonion : IsAlternative RealOctonion := inferInstance

/-- **The norm of `𝕆` is positive definite** — the sum of eight squares. -/
theorem posDef_realOctonion : realOctonion.norm.PosDef :=
  posDef_cay₈ ℝ (by norm_num) (by norm_num) (by norm_num)

/-- **`𝕆` is a division algebra.** -/
theorem exists_inv_realOctonion {x : RealOctonion} (hx : x ≠ 0) :
    ∃ y, x * y = 1 ∧ y * x = 1 :=
  exists_inv_cay₈ ℝ (by norm_num) (by norm_num) (by norm_num) hx

/-! ### Where the tower breaks

`ℍ` is not commutative and `𝕆` is not associative, with explicit witnesses. These are what stop
the tower: `ConicAlgebra.mul_assoc_cay` needs its input commutative, so `𝕆` gets no `Ring`
structure, and `ConicAlgebra.isMultiplicative_cay` and `ConicAlgebra.isAlternative_cay` need their
input associative, so the sedenions `Cay(𝕆, μ)` get neither a multiplicative norm nor
alternativity. -/

/-- The conjugation of `ℂ` moves `i`, which is what makes `ℍ` non-commutative. -/
theorem conj_i_ne_i : (cay₂ ℝ (-1)).conj ((0, 1) : ℝ × ℝ) ≠ ((0, 1) : ℝ × ℝ) := by
  have hc : (cay₂ ℝ (-1)).conj ((0, 1) : ℝ × ℝ) =
      (((baseRing ℝ).conj 0, -(1 : ℝ)) : ℝ × ℝ) :=
    cay_conj_apply _
  intro hcon
  rw [hc] at hcon
  have h2 := congrArg Prod.snd hcon
  norm_num at h2

/-- **`ℍ` is not commutative.** -/
theorem exists_mul_ne_mul_realQuaternion : ∃ x y : RealQuaternion, x * y ≠ y * x :=
  exists_mul_ne_mul_cay _ _ conj_i_ne_i

/-- **`𝕆` is not associative** — so the tower cannot be continued by the theorems that built
it,
and the sedenions are neither alternative nor multiplicative. -/
theorem exists_mul_mul_ne_mul_mul_realOctonion :
    ∃ x y z : RealOctonion, x * y * z ≠ x * (y * z) :=
  let ⟨_, _, h⟩ := exists_mul_ne_mul_realQuaternion
  exists_mul_mul_ne_mul_mul_cay _ _ (conjIsInvolution_cay₄ ℝ (-1) (-1)) h

/-- **`𝕆` is a composition algebra** of rank 8 over `ℝ`. -/
theorem isComposition_realOctonion : realOctonion.IsComposition.{0, 0, 0} :=
  letI : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
  isComposition_cay₈ ℝ (-1) (-1) (-1) (IsUnit.neg isUnit_one) (IsUnit.neg isUnit_one)
    (IsUnit.neg isUnit_one)

end ConicAlgebra
