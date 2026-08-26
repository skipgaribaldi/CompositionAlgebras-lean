/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Unimodular elements of a module

Defines `IsUnimodular R m` for an element `m` of an `R`-module `M`: `R·m` is free of rank 1 and a
direct summand of `M` (`GPR 9.13`).

This is not a norm-theoretic notion — no quadratic form is in sight here — but it is the piece
`QuadraticForm/Isotropic.lean` needs to state GPR-sense isotropy correctly (`GPR 11.17`): a
**unimodular** null vector, not merely a nonzero one. See `AGENTS.md` §6(c).

## Main definitions

* `IsUnimodular` : `R·m` is free of rank 1 (`toSpanSingleton` injective) and a direct summand of
  `M` (`Submodule.span R {m}` is complemented).

## Main results

* `isUnimodular_one` : `1` is unimodular in `R` itself, the basic example.
* `IsUnimodular.map` : unimodularity transports along a linear equivalence.
* `IsUnimodular.units_smul` : unimodularity is unaffected by scaling by a unit.
* `isUnimodular_of_ne_zero` : over a field, unimodular is *exactly* nonzero — every nonzero vector
  in a vector space spans a complemented line. This is what collapses GPR-sense isotropy onto
  mathlib's `Anisotropic` over a field; see `QuadraticForm/Isotropic.lean`.

## Implementation notes

GPR states unimodularity geometrically: `m` is unimodular iff `m ⊗ 1_{κ(𝔭)} ≠ 0` for every
`𝔭 ∈ Spec R` (i.e. `m` survives in every residue field). `GPR 9.17` shows this is equivalent to
the algebraic formulation used here, which is the one that type-checks without first setting up
residue fields, so it is what we take as the definition; the geometric form is not (yet) proved
equivalent in this file. Doing so needs the same "nonzero in a f.g. projective module survives in
some residue field" fact that underlies `QuadraticForm/BaseChangeProjective.lean` and the missing
half of `QuadraticForm/Regularity.lean` (`GN (C.8.1)`) — see that file's implementation notes.

We reuse mathlib's general lattice notion `IsComplemented` (`Mathlib.Order.Disjoint`) for
"direct summand" rather than inventing a submodule-specific one, per `AGENTS.md` §0.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 9.13, 9.17, 11.24.
-/

universe u v

/-- `m` is **unimodular** in the `R`-module `M`: the cyclic submodule `R·m` is free of rank 1
(equivalently, `r • m = 0 → r = 0`) and a direct summand of `M` (`GPR 9.13`). -/
def IsUnimodular (R : Type u) [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] (m : M) :
    Prop :=
  Function.Injective (LinearMap.toSpanSingleton R M m) ∧ IsComplemented (Submodule.span R {m})

variable {R : Type u} [CommRing R]

/-- `1` is unimodular in `R` viewed as a module over itself: `R·1 = R`, free of rank 1 and (as the
whole module) trivially a direct summand. -/
theorem isUnimodular_one : IsUnimodular R (1 : R) := by
  constructor
  · intro a b hab
    simpa using hab
  · have h1 : Submodule.span R ({1} : Set R) = ⊤ :=
      (Submodule.span_singleton_eq_top_iff R (1 : R)).mpr fun v ↦ ⟨v, by simp⟩
    rw [h1]
    exact isComplemented_top

/-- A linear equivalence carries a complementary pair of submodules to a complementary pair:
`Submodule.map` along an equivalence preserves `IsCompl`. -/
private theorem isCompl_map_of_linearEquiv {M : Type*} [AddCommGroup M] [Module R M]
    {M' : Type*} [AddCommGroup M'] [Module R M'] {N N' : Submodule R M} (h : IsCompl N N')
    (e : M ≃ₗ[R] M') : IsCompl (N.map e.toLinearMap) (N'.map e.toLinearMap) := by
  constructor
  · rw [disjoint_iff, ← Submodule.map_inf e.toLinearMap e.injective, h.inf_eq_bot,
      Submodule.map_bot]
  · rw [codisjoint_iff, ← Submodule.map_sup, h.sup_eq_top]
    exact Submodule.map_eq_top_iff.mpr rfl

/-- Unimodularity transports along a linear equivalence: `m` unimodular in `M` and `e : M ≃ₗ N`
give `e m` unimodular in `N`. -/
theorem IsUnimodular.map {M : Type*} [AddCommGroup M] [Module R M]
    {M' : Type*} [AddCommGroup M'] [Module R M'] {m : M}
    (hm : IsUnimodular R m) (e : M ≃ₗ[R] M') : IsUnimodular R (e m) := by
  refine ⟨?_, ?_⟩
  · have heq : LinearMap.toSpanSingleton R M' (e m) =
      e.toLinearMap ∘ₗ LinearMap.toSpanSingleton R M m := by
      ext
      simp [LinearMap.toSpanSingleton_apply]
    rw [heq]
    exact e.injective.comp hm.1
  · obtain ⟨N, hN⟩ := hm.2
    refine ⟨N.map e.toLinearMap, ?_⟩
    have hspan : Submodule.span R {e m} = (Submodule.span R {m}).map e.toLinearMap := by
      rw [Submodule.map_span]
      congr 1
      simp
    rw [hspan]
    exact isCompl_map_of_linearEquiv hN e

/-- Unimodularity is unaffected by scaling by a unit: if `m` is unimodular then so is `u • m` for
`u : Rˣ`, since `R·(u • m) = R·m`. -/
theorem IsUnimodular.units_smul {M : Type*} [AddCommGroup M] [Module R M] {m : M}
    (hm : IsUnimodular R m) (u : Rˣ) : IsUnimodular R (u • m) := by
  have hu : (u • m : M) = (u : R) • m := rfl
  refine ⟨?_, ?_⟩
  · have heq : LinearMap.toSpanSingleton R M ((u : R) • m) =
      LinearMap.toSpanSingleton R M m ∘ₗ LinearMap.toSpanSingleton R R (u : R) := by
      ext
      simp [LinearMap.toSpanSingleton_apply, mul_comm]
    rw [hu, heq]
    exact hm.1.comp u.isUnit.mul_left_injective
  · rw [hu, Submodule.span_singleton_smul_eq u.isUnit m]
    exact hm.2

/-- Over a field, unimodular is exactly nonzero: every nonzero vector spans a line, and every
subspace of a vector space has a complement. -/
theorem isUnimodular_of_ne_zero {K : Type u} [Field K] {M : Type v} [AddCommGroup M]
    [Module K M] {x : M} (hx : x ≠ 0) : IsUnimodular K x := by
  refine ⟨fun a b hab ↦ ?_, Submodule.exists_isCompl (Submodule.span K {x})⟩
  have hsub : (a - b) • x = 0 := by
    have := sub_eq_zero.mpr hab
    simpa [sub_smul, LinearMap.toSpanSingleton_apply] using this
  rcases smul_eq_zero.mp hsub with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hx

/-! ### The functional characterization (`GPR 9.17`)

`m` is unimodular exactly when some linear functional takes the value `1` on it. This is the form
in which unimodular elements get *produced*: a construction that exhibits a functional hitting `1`
(as the LG argument of `GN 2.6(a)` does) immediately yields unimodularity. -/

/-- A functional taking the value `1` on `m` makes `m` unimodular: it splits off `R·m` with
complement its kernel, and it witnesses `r • m = 0 → r = 0`. -/
theorem isUnimodular_of_exists_linearMap_apply_eq_one {M : Type v} [AddCommGroup M] [Module R M]
    {m : M} (l : M →ₗ[R] R) (hl : l m = 1) : IsUnimodular R m := by
  have hinj : Function.Injective (LinearMap.toSpanSingleton R M m) := by
    intro a b hab
    have h := congrArg l hab
    simpa [LinearMap.toSpanSingleton_apply, hl] using h
  refine ⟨hinj, LinearMap.ker l, ?_, ?_⟩
  · rw [disjoint_iff_inf_le]
    rintro x ⟨hx1, hx2⟩
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hx1
    have hr : r = 0 := by
      have := LinearMap.mem_ker.mp hx2
      simpa [hl] using this
    simp [hr]
  · rw [codisjoint_iff_le_sup]
    intro x _
    refine Submodule.mem_sup.mpr ⟨l x • m, Submodule.mem_span_singleton.mpr ⟨l x, rfl⟩,
      x - l x • m, ?_, by abel⟩
    simp [LinearMap.mem_ker, hl]

/-- Conversely, a unimodular element is hit by a functional: project onto `R·m` along a
complement and undo the isomorphism `R ≃ R·m`. -/
theorem IsUnimodular.exists_linearMap_apply_eq_one {M : Type v} [AddCommGroup M] [Module R M]
    {m : M} (hm : IsUnimodular R m) : ∃ l : M →ₗ[R] R, l m = 1 := by
  obtain ⟨hinj, N, hN⟩ := hm
  have hrange : Submodule.span R {m} = LinearMap.range (LinearMap.toSpanSingleton R M m) := by
    rw [LinearMap.span_singleton_eq_range]
  let e : R ≃ₗ[R] (Submodule.span R {m}) :=
    (LinearEquiv.ofInjective _ hinj).trans (LinearEquiv.ofEq _ _ hrange.symm)
  refine ⟨(e.symm : (Submodule.span R {m}) →ₗ[R] R) ∘ₗ
    Submodule.projectionOnto _ _ hN, ?_⟩
  have hmem : m ∈ Submodule.span R {m} := Submodule.mem_span_singleton_self m
  have hproj : Submodule.projectionOnto _ _ hN m = ⟨m, hmem⟩ :=
    Submodule.projectionOnto_apply_left hN ⟨m, hmem⟩
  have he : e 1 = ⟨m, hmem⟩ := by
    apply Subtype.ext
    simp [e, LinearMap.toSpanSingleton_apply]
  rw [LinearMap.comp_apply, hproj, ← he]
  exact e.symm_apply_apply 1

/-- **`GPR 9.17`**, the algebraic half: unimodularity is exactly being hit by a functional. -/
theorem isUnimodular_iff_exists_linearMap_apply_eq_one {M : Type v} [AddCommGroup M] [Module R M]
    {m : M} : IsUnimodular R m ↔ ∃ l : M →ₗ[R] R, l m = 1 :=
  ⟨IsUnimodular.exists_linearMap_apply_eq_one,
    fun ⟨l, hl⟩ ↦ isUnimodular_of_exists_linearMap_apply_eq_one l hl⟩

/-! ### Splitting off a unimodular element

A unimodular element does not merely span a complemented line — it splits `M` as `R ⊕ M'` with the
free factor *identified*, which is what an induction on the rank needs. -/

variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The **splitting** determined by a functional `l` with `l m = 1`: `M ≃ R × ker l`, by
`x ↦ (l x, x - l x • m)` with inverse `(r, y) ↦ r • m + y`.

Together with `isUnimodular_iff_exists_linearMap_apply_eq_one` this says a unimodular element
splits off a free rank-one direct summand. The complement is presented concretely as `ker l`
rather than as an abstract summand so that it stays a `Submodule R M`, hence lives in the same
universe as `M` — which is what makes the induction on the rank in
`Module.free_of_rankAtStalk_eq` (`LGRing/ConstantRank.lean`) go through. -/
noncomputable def LinearMap.equivProdKerOfApplyEqOne (l : M →ₗ[R] R) (m : M) (hl : l m = 1) :
    M ≃ₗ[R] R × (LinearMap.ker l) :=
  LinearEquiv.ofLinearMap
    (l.prod ((LinearMap.id - (LinearMap.toSpanSingleton R M m) ∘ₗ l).codRestrict _ fun x ↦ by
      simp [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, hl]))
    ((LinearMap.toSpanSingleton R M m).coprod (LinearMap.ker l).subtype)
    (by
      refine LinearMap.ext fun x ↦ ?_
      obtain ⟨r, y, hy⟩ := x
      have hfst : l (r • m + y) = r := by
        simp [LinearMap.mem_ker.mp hy, hl]
      refine Prod.ext ?_ (Subtype.ext ?_) <;>
        simp [LinearMap.toSpanSingleton_apply, hfst]
      · simp [LinearMap.mem_ker.mp hy, hl])
    (by refine LinearMap.ext fun x ↦ ?_; simp)

@[simp]
theorem LinearMap.equivProdKerOfApplyEqOne_symm_apply (l : M →ₗ[R] R) (m : M) (hl : l m = 1)
    (x : R × (LinearMap.ker l)) :
    (LinearMap.equivProdKerOfApplyEqOne l m hl).symm x = x.1 • m + (x.2 : M) :=
  rfl

/-- A unimodular element splits `M` as `R ⊕ M'` for a submodule `M'` of `M`. -/
theorem IsUnimodular.exists_linearEquiv_prod {m : M} (hm : IsUnimodular R m) :
    ∃ M' : Submodule R M, Nonempty (M ≃ₗ[R] R × M') := by
  obtain ⟨l, hl⟩ := hm.exists_linearMap_apply_eq_one
  exact ⟨LinearMap.ker l, ⟨LinearMap.equivProdKerOfApplyEqOne l m hl⟩⟩
