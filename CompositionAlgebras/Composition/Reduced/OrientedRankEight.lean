/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import CompositionAlgebras.Composition.Reduced.Orientation
public import CompositionAlgebras.Composition.Reduced.RankEight
public import CompositionAlgebras.Module.ExteriorPower

/-!
# Reduced octonion algebras are oriented twisted Zorn algebras (`GPR 22.15`)

`GPR 22.14` attaches to an orientation `θ : ⋀³ M ≅ k` of a finitely generated projective module
`M` of rank three its two associated vector products, and with them the algebra `Zor(M, θ)` of
twisted Zorn vector matrices. `GPR 22.15` (Petersson) says that up to isomorphism these are exactly
the reduced octonion algebras, an isomorphism `Zor(M, θ) ≅ C` matching the matrix unit `e₁₁` with
a given elementary idempotent `c`.

The ingredients are proved elsewhere. `Composition/Reduced/Orientation.lean` builds the pair of
an orientation, `Module.VectorProductPair.ofOrientation`; `Composition/Reduced/TwistedZorn.lean`
shows that the twisted Zorn algebra of any pair is a reduced composition algebra; and
`Composition/Reduced/RankEight.lean` proves the converse with the pair *read off* from Peirce
multiplication on `M = C₂₁`, with no orientation in sight
(`IsElementaryIdempotent.isomorphic_twistedZor_of_rankAtStalk_eq_eight`).
This file supplies the bridge: on a finite projective module of constant rank three, **every**
vector-product pair is `ofOrientation` of exactly one orientation, namely its volume form
`u ∧ v ∧ w ↦ ⟨u × v, w⟩`. For the Peirce pair that volume form is `n_C(uv, w)`, which is the
orientation `GPR (22.15.3)` writes down.

The bridge is module theory and never looks at the algebra. Base change along any commutative
`k`-algebra carries a pair to a pair (`Module.VectorProductPair.baseChange`, with the dual handled
by `GPR 9.15`). At a maximal ideal the module is free, so the base-changed pair is the pair of a
basis (`Module.VectorProductPair.exists_eq_ofBasis`) and its two volume forms multiply to the
determinant of pairings; descending from all maximal ideals gives that triple identity,
`GPR (22.14.1)`, over `k`. The volume form `⋀³ M → k` is then surjective, because on a local basis
its value is a unit, and injective, because by the triple identity and the perfect pairing
`GPR 21.7` every functional on the projective module `⋀³ M` is a multiple of it. Applying the triple
identity once to the pair and once to the dual orientation `θ*⁻¹` identifies the dual products.

⚠ **Not `GPR`'s proof.** `GPR 22.15` shows that `θ` is bijective using the algebra: over a field,
`θ = 0` would force `M² = 0`, which linearized right alternativity rules out, and over a local
ring one passes to the residue field. It then identifies the dual product using the Moufang
identities. The argument here needs only the vector-product axioms, so it applies to every pair
on a constant-rank-three module, not only to Peirce pairs.

⚠ **Orientation** means `GPR`'s notion, a linear isomorphism `⋀³ M ≃ k` (`GPR 21.8`, `22.14`), not
mathlib's `Orientation`, which is a ray of volume forms.

## Main definitions

* `Module.VectorProductPair.baseChange` : the scalar extension of a vector-product pair on a
  finite projective module.
* `Module.VectorProductPair.orientation` : the orientation `⋀³ M ≃ k` of a vector-product pair on
  a constant-rank-three finite projective module.
* `Module.VectorProductPair.orientationEquiv` : orientations and vector-product pairs correspond.

## Main results

* `Module.VectorProductPair.crossAlternating_mul_crossDualAlternating` : the triple identity
  `GPR (22.14.1)` for an arbitrary pair.
* `Module.VectorProductPair.ofOrientation_orientation` : every pair is induced by its orientation;
  `Module.VectorProductPair.orientation_ofOrientation` : and that orientation is unique.
* `ConicAlgebra.IsElementaryIdempotent.exists_orientation_isometryEquiv_twistedZor` :
  **`GPR 22.15`** for a given elementary idempotent, with the orientation `GPR (22.15.3)` and the
  normalization `GPR (22.15.1)`.
* `ConicAlgebra.IsElementaryIdempotent.exists_orientation_isomorphic_twistedZor`,
  `ConicAlgebra.IsElementaryIdempotent.exists_isomorphic_twistedZor_ofOrientation` : the
  isomorphism alone, on the Peirce component and in `GPR`'s form "for some `M` and `θ`".
* `ConicAlgebra.exists_isomorphic_twistedZor_ofOrientation_iff` : **`GPR 22.15`**, both
  directions: the algebras `Zor(M, θ)` are exactly the composition algebras of constant rank
  eight with an elementary idempotent.

## Implementation notes

The module-theoretic part (everything in `namespace Module`, and the instance
`exteriorPower.instProjective`) uses no composition algebra. It cannot live in `Module/`, which
imports mathlib only, because it uses `Module.Dual.baseChangeEquivOfProjective` from
`QuadraticForm/Regularity.lean` and `VectorProductPair.ofOrientation`; it sits with the latter
in `Composition/Reduced/`.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 9.15, 21.7, 21.8,
  22.7, 22.14, 22.15.
-/

@[expose] public section

universe u v w

open scoped TensorProduct

/-- The exterior powers of a projective module are projective. -/
instance exteriorPower.instProjective {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M]
    [Module R M] [Module.Projective R M] (n : ℕ) : Module.Projective R (⋀[R]^n M) := by
  obtain ⟨s, hs⟩ := Module.projective_def'.mp ‹Module.Projective R M›
  exact Module.Projective.of_split (exteriorPower.map n s)
    (exteriorPower.map n (Finsupp.linearCombination R id))
    (by rw [← exteriorPower.map_comp, hs, exteriorPower.map_id])

namespace Module

/-- In the coordinates of a finite basis and its dual basis, the product of the two determinant
forms is the determinant of the matrix of pairings. -/
theorem Basis.det_mul_det_dualBasis {R : Type u} [CommRing R] {N : Type v} [AddCommGroup N]
    [Module R N] {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R N)
    (x : ι → N) (f : ι → Module.Dual R N) :
    b.det x * b.dualBasis.det f = Matrix.det (.of fun i j ↦ f i (x j)) := by
  rw [Basis.det_apply, Basis.det_apply, mul_comm,
    ← Matrix.det_transpose (b.dualBasis.toMatrix f), ← Matrix.det_mul]
  congr 1
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply, Basis.toMatrix_apply, Basis.dualBasis_repr, Matrix.of_apply]
  conv_rhs => rw [← b.sum_repr (x j)]
  simp only [map_sum, map_smul, smul_eq_mul, mul_comm]

namespace VectorProductPair

variable {k : Type u} {M : Type v} [CommRing k] [AddCommGroup M] [Module k M]
  (P : VectorProductPair k M)

/-- The trilinear form of the dual vector product, read with its last argument as the
functional: `⟨χ, φ × ψ⟩`. -/
theorem crossDualAlternating_apply_cycle (φ ψ χ : Module.Dual k M) :
    P.crossDualAlternating ![φ, ψ, χ] = χ (P.crossDual φ ψ) := by
  rw [alternating_fin_three_cycle, alternating_fin_three_cycle]
  simp

/-- The linear form on `⋀³ M` induced by the volume form `(u, v, w) ↦ ⟨u × v, w⟩` of a
vector-product pair. -/
noncomputable def orientationLinearMap : ⋀[k]^3 M →ₗ[k] k :=
  exteriorPower.alternatingMapLinearEquiv P.crossAlternating

@[simp] theorem orientationLinearMap_ιMulti (x : Fin 3 → M) :
    P.orientationLinearMap (exteriorPower.ιMulti k 3 x) = P.crossAlternating x :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ x

section BaseChange

variable [Module.Finite k M] [Module.Projective k M] (S : Type w) [CommRing S] [Algebra k S]

/-- The dual vector product of the base change of a vector-product pair: the curried scalar
extension of the dual volume form, transported along the projective dual-base-change
equivalence `GPR 9.15` and read back in `S ⊗ M` by reflexivity. -/
noncomputable def baseChangeCrossDual :
    Module.Dual S (S ⊗[k] M) →ₗ[S] Module.Dual S (S ⊗[k] M) →ₗ[S] S ⊗[k] M :=
  (AlternatingMap.curryFinThree
    ((AlternatingMap.baseChangeAlternatingFinThree (S := S) P.crossDualAlternating).compLinearMap
      (Module.Dual.baseChangeEquivOfProjective (R := k) (M := M) (A := S)).symm.toLinearMap)).compr₂
    (Module.evalEquiv S (S ⊗[k] M)).symm.toLinearMap

/-- The defining property of the base-changed dual vector product: `⟨χ, φ × ψ⟩` is the scalar
extension of the dual volume form evaluated at `(φ, ψ, χ)`, read in `S ⊗ M*`. This is the rule
`θ*⁻¹(φ ∧ ψ ∧ χ) = ⟨χ, φ × ψ⟩` of `GPR (22.14.2)`. -/
theorem apply_baseChangeCrossDual (f g h : Module.Dual S (S ⊗[k] M)) :
    h (P.baseChangeCrossDual S f g) =
      AlternatingMap.baseChangeFinThree (S := S) P.crossDualAlternating
        ((Module.Dual.baseChangeEquivOfProjective (R := k) (M := M) (A := S)).symm f)
        ((Module.Dual.baseChangeEquivOfProjective (R := k) (M := M) (A := S)).symm g)
        ((Module.Dual.baseChangeEquivOfProjective (R := k) (M := M) (A := S)).symm h) := by
  change Module.evalEquiv S (S ⊗[k] M) ((Module.evalEquiv S (S ⊗[k] M)).symm _) h = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- The base-changed dual vector product on pure tensors. -/
theorem baseChangeCrossDual_tmul (r s : S) (φ ψ : Module.Dual k M) :
    P.baseChangeCrossDual S (Module.Dual.baseChangeTensor S (r ⊗ₜ[k] φ))
      (Module.Dual.baseChangeTensor S (s ⊗ₜ[k] ψ)) = (r * s) ⊗ₜ[k] P.crossDual φ ψ := by
  let e := Module.Dual.baseChangeEquivOfProjective (R := k) (M := M) (A := S)
  apply (Module.evalEquiv S (S ⊗[k] M)).injective
  ext h
  rw [Module.evalEquiv_apply, Module.evalEquiv_apply, Module.Dual.eval_apply,
    Module.Dual.eval_apply, apply_baseChangeCrossDual,
    ← Module.Dual.baseChangeEquivOfProjective_apply,
    ← Module.Dual.baseChangeEquivOfProjective_apply, LinearEquiv.symm_apply_apply,
    LinearEquiv.symm_apply_apply]
  obtain ⟨q, rfl⟩ := e.surjective h
  rw [LinearEquiv.symm_apply_apply]
  induction q using TensorProduct.inductionOn with
  | add q₁ q₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply]; rw [h₁, h₂]
  | tmul t χ =>
    rw [AlternatingMap.baseChangeFinThree_tmul, crossDualAlternating_apply_cycle]
    simp only [e, Module.Dual.baseChangeEquivOfProjective_apply, Module.Dual.baseChangeTensor_tmul]
    ring

/-- **Base change of a vector-product pair** along a commutative `k`-algebra `S`, for `M` finitely
generated projective. The first product is the scalar extension of the volume form
`(u, v, w) ↦ ⟨u × v, w⟩`; the second is the scalar extension of the dual volume form, read
through the identification `S ⊗ M* = (S ⊗ M)*` of `GPR 9.15`. The axioms are checked on pure
tensors. -/
noncomputable def baseChange : VectorProductPair S (S ⊗[k] M) where
  cross := AlternatingMap.baseChangeFinThree (S := S) P.crossAlternating
  crossDual := P.baseChangeCrossDual S
  cross_self v := LinearMap.ext fun w ↦ by
    rw [AlternatingMap.baseChangeFinThree_self_zero_one]
    rfl
  crossDual_self f := by
    apply (Module.evalEquiv S (S ⊗[k] M)).injective
    ext h
    rw [Module.evalEquiv_apply, Module.Dual.eval_apply, apply_baseChangeCrossDual,
      AlternatingMap.baseChangeFinThree_self_zero_one, map_zero, LinearMap.zero_apply]
  cross_apply_left v w := AlternatingMap.baseChangeFinThree_self_zero_two _ v w
  apply_crossDual_left f g := by
    rw [apply_baseChangeCrossDual, AlternatingMap.baseChangeFinThree_self_zero_two]
  cross_apply_crossDual v w f g := by
    let e := Module.Dual.baseChangeEquivOfProjective (R := k) (M := M) (A := S)
    obtain ⟨q, rfl⟩ := e.surjective f
    obtain ⟨q', rfl⟩ := e.surjective g
    induction q using TensorProduct.inductionOn with
    | add q₁ q₂ h₁ h₂ =>
      simp only [map_add, LinearMap.add_apply] at h₁ h₂ ⊢
      rw [h₁, h₂]
      ring
    | tmul r φ =>
      induction q' using TensorProduct.inductionOn with
      | add q₁ q₂ h₁ h₂ =>
        simp only [map_add, LinearMap.add_apply] at h₁ h₂ ⊢
        rw [h₁, h₂]
        ring
      | tmul s ψ =>
        simp only [e, Module.Dual.baseChangeEquivOfProjective_apply]
        rw [baseChangeCrossDual_tmul]
        induction v using TensorProduct.inductionOn with
        | add v₁ v₂ h₁ h₂ =>
          simp only [map_add, LinearMap.add_apply] at h₁ h₂ ⊢
          rw [h₁, h₂]
          ring
        | tmul t x =>
          induction w using TensorProduct.inductionOn with
          | add w₁ w₂ h₁ h₂ =>
            simp only [map_add, LinearMap.add_apply] at h₁ h₂ ⊢
            rw [h₁, h₂]
            ring
          | tmul t' y =>
            rw [AlternatingMap.baseChangeFinThree_tmul]
            simp only [Module.Dual.baseChangeTensor_tmul]
            have h := P.cross_apply_crossDual x y φ ψ
            simp only [crossAlternating_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
              Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, h, map_sub, map_mul]
            ring

@[simp] theorem baseChange_cross :
    (P.baseChange S).cross = AlternatingMap.baseChangeFinThree (S := S) P.crossAlternating := rfl

@[simp] theorem baseChange_crossDual : (P.baseChange S).crossDual = P.baseChangeCrossDual S := rfl

/-- The volume form of the base change is the scalar extension of the volume form. -/
theorem crossAlternating_baseChange :
    (P.baseChange S).crossAlternating =
      AlternatingMap.baseChangeAlternatingFinThree (S := S) P.crossAlternating :=
  rfl

/-- The volume form of the base change on scalar extensions of vectors of `M`. -/
theorem crossAlternating_baseChange_one_tmul (x : Fin 3 → M) :
    (P.baseChange S).crossAlternating (fun i ↦ 1 ⊗ₜ[k] x i) =
      algebraMap k S (P.crossAlternating x) := by
  have hx : ![x 0, x 1, x 2] = x := by
    ext i
    fin_cases i <;> rfl
  rw [crossAlternating_apply, baseChange_cross, AlternatingMap.baseChangeFinThree_tmul, hx]
  ring

/-- The dual volume form of the base change on scalar extensions of functionals on `M`. -/
theorem crossDualAlternating_baseChange_one_tmul (f : Fin 3 → Module.Dual k M) :
    (P.baseChange S).crossDualAlternating
        (fun i ↦ Module.Dual.baseChangeTensor S (1 ⊗ₜ[k] f i)) =
      algebraMap k S (P.crossDualAlternating f) := by
  rw [crossDualAlternating_apply, baseChange_crossDual, baseChangeCrossDual_tmul,
    Module.Dual.baseChangeTensor_tmul, crossDualAlternating_apply]
  ring

end BaseChange

/-- **The triple identity in the free case.** For a vector-product pair on a module with a basis
of size three, the volume forms of the two products multiply to the determinant of the matrix of
pairings: this is `GPR (22.14.1)` read for the pair. -/
theorem crossAlternating_mul_crossDualAlternating_of_basis (b : Module.Basis (Fin 3) k M)
    (x : Fin 3 → M) (f : Fin 3 → Module.Dual k M) :
    P.crossAlternating x * P.crossDualAlternating f = Matrix.det (.of fun i j ↦ f i (x j)) := by
  obtain ⟨b', rfl⟩ := VectorProductPair.exists_eq_ofBasis b P
  rw [VectorProductPair.crossAlternating_ofBasis, VectorProductPair.crossDualAlternating_ofBasis]
  exact b'.det_mul_det_dualBasis x f

end VectorProductPair

/-- A finitely generated projective module of constant rank `n` becomes free of rank `n` at every
prime. -/
theorem nonempty_basis_atPrime_of_rankAtStalk_eq {k : Type u} {M : Type v} [CommRing k]
    [AddCommGroup M] [Module k M] [Module.Finite k M] [Module.Projective k M] {n : ℕ}
    (hM : Module.rankAtStalk (R := k) M = fun _ ↦ n) (J : Ideal k) [J.IsPrime] :
    Nonempty (Module.Basis (Fin n) (Localization.AtPrime J)
      (Localization.AtPrime J ⊗[k] M)) := by
  let S := Localization.AtPrime J
  let : Module.Free S (S ⊗[k] M) := Module.free_of_flat_of_isLocalRing
  have hfin : Module.finrank S (S ⊗[k] M) = n := by
    have h := congrFun hM ⟨J, inferInstance⟩
    rw [Module.rankAtStalk_eq_finrank_tensorProduct] at h
    simpa [S] using h
  exact ⟨Module.finBasisOfFinrankEq S (S ⊗[k] M) hfin⟩

namespace VectorProductPair

variable {k : Type u} {M : Type v} [CommRing k] [AddCommGroup M] [Module k M]
  [Module.Finite k M] [Module.Projective k M] (P : VectorProductPair k M)

/-- **The triple identity**, `GPR (22.14.1)` for a vector-product pair on a constant-rank-three
finite projective module: `⟨u × v, w⟩ · ⟨φ, ψ × χ⟩ = det (⟨φᵢ, vⱼ⟩)`. It is checked at every
maximal ideal, where the module is free and the based case
`crossAlternating_mul_crossDualAlternating_of_basis` applies to the base-changed pair. -/
theorem crossAlternating_mul_crossDualAlternating
    (hM : Module.rankAtStalk (R := k) M = fun _ ↦ 3) (x : Fin 3 → M)
    (f : Fin 3 → Module.Dual k M) :
    P.crossAlternating x * P.crossDualAlternating f = Matrix.det (.of fun i j ↦ f i (x j)) := by
  apply sub_eq_zero.mp
  apply eq_zero_of_localization
  intro J hJ
  let S := Localization.AtPrime J
  obtain ⟨b⟩ := nonempty_basis_atPrime_of_rankAtStalk_eq hM J
  have h := (P.baseChange S).crossAlternating_mul_crossDualAlternating_of_basis b
    (fun i ↦ 1 ⊗ₜ[k] x i) (fun i ↦ Module.Dual.baseChangeTensor S (1 ⊗ₜ[k] f i))
  rw [crossAlternating_baseChange_one_tmul, crossDualAlternating_baseChange_one_tmul] at h
  rw [map_sub, map_mul, h, RingHom.map_det, sub_eq_zero]
  congr 1
  ext i j
  simp only [Module.Dual.baseChangeTensor_tmul, one_mul]
  rfl

/-- The volume form of a vector-product pair on a constant-rank-three finite projective module is
surjective. At a maximal ideal `J`, the base-changed pair has a unit volume on a basis
(`isUnit_crossAlternating_basis`), which could not happen if every volume of `M` lay in `J`. -/
theorem surjective_orientationLinearMap (hM : Module.rankAtStalk (R := k) M = fun _ ↦ 3) :
    Function.Surjective P.orientationLinearMap := by
  rw [← LinearMap.range_eq_top]
  by_contra hne
  obtain ⟨J, hJ, hle⟩ := Ideal.exists_le_maximal _ hne
  have hval (x : Fin 3 → M) : P.crossAlternating x ∈ J :=
    hle ⟨exteriorPower.ιMulti k 3 x, P.orientationLinearMap_ιMulti x⟩
  let S := Localization.AtPrime J
  obtain ⟨b⟩ := nonempty_basis_atPrime_of_rankAtStalk_eq hM J
  have hmem (y₀ y₁ y₂ : S ⊗[k] M) :
      AlternatingMap.baseChangeFinThree (S := S) P.crossAlternating y₀ y₁ y₂ ∈
        Ideal.map (algebraMap k S) J := by
    induction y₀ using TensorProduct.inductionOn with
    | add a a' ha ha' =>
      rw [map_add, LinearMap.add_apply, LinearMap.add_apply]
      exact add_mem ha ha'
    | tmul r x =>
      induction y₁ using TensorProduct.inductionOn with
      | add a a' ha ha' =>
        rw [map_add, LinearMap.add_apply]
        exact add_mem ha ha'
      | tmul s y =>
        induction y₂ using TensorProduct.inductionOn with
        | add a a' ha ha' =>
          rw [map_add]
          exact add_mem ha ha'
        | tmul t z =>
          rw [AlternatingMap.baseChangeFinThree_tmul]
          exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (hval _))
  have hunit := (P.baseChange S).isUnit_crossAlternating_basis b
  have hmax : (P.baseChange S).crossAlternating b ∈ IsLocalRing.maximalIdeal S := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact hmem (b 0) (b 1) (b 2)
  exact (IsLocalRing.mem_maximalIdeal _).mp hmax hunit

/-- The volume form of a vector-product pair on a constant-rank-three finite projective module is
injective. By the triple identity, every functional on `⋀³ M` — all of which come from `⋀³ M*`
by `GPR 21.7` — is a multiple of the volume form, and functionals separate the points of the
projective module `⋀³ M`. -/
theorem injective_orientationLinearMap (hM : Module.rankAtStalk (R := k) M = fun _ ↦ 3) :
    Function.Injective P.orientationLinearMap := by
  let B : ⋀[k]^3 (Module.Dual k M) →ₗ[k] k :=
    exteriorPower.alternatingMapLinearEquiv P.crossDualAlternating
  have hpair (η : ⋀[k]^3 (Module.Dual k M)) (ω : ⋀[k]^3 M) :
      exteriorPower.pairingDual k M 3 η ω = P.orientationLinearMap ω * B η := by
    have h₁ (x : Fin 3 → M) :
        Module.Dual.eval k _ (exteriorPower.ιMulti k 3 x) ∘ₗ exteriorPower.pairingDual k M 3 =
          P.crossAlternating x • B := by
      ext f
      simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
        Module.Dual.eval_apply, exteriorPower.pairingDual_ιMulti_ιMulti, LinearMap.smul_apply,
        B, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, smul_eq_mul,
        P.crossAlternating_mul_crossDualAlternating hM]
      rw [show (Matrix.of fun i j ↦ f j (x i)) =
        Matrix.transpose (Matrix.of fun i j ↦ f i (x j)) by rfl, Matrix.det_transpose]
    have h₂ : exteriorPower.pairingDual k M 3 η = B η • P.orientationLinearMap := by
      ext x
      simpa [mul_comm] using LinearMap.congr_fun (h₁ x) η
    rw [h₂, LinearMap.smul_apply, smul_eq_mul, mul_comm]
  refine (injective_iff_map_eq_zero _).mpr fun ω hω ↦ ?_
  refine (Module.forall_dual_apply_eq_zero_iff k ω).mp fun φ ↦ ?_
  obtain ⟨η, rfl⟩ := (exteriorPower.pairingDual_bijective_of_projective (M := M) 3).2 φ
  rw [hpair, hω, zero_mul]

/-- **The orientation of a vector-product pair.** On a finite projective module of constant rank
three, the volume form `u ∧ v ∧ w ↦ ⟨u × v, w⟩` of a vector-product pair is an orientation
`⋀³ M ≃ k`; this is the converse of the construction of `GPR 22.14`. -/
noncomputable def orientation (hM : Module.rankAtStalk (R := k) M = fun _ ↦ 3) :
    (⋀[k]^3 M) ≃ₗ[k] k :=
  LinearEquiv.ofBijective P.orientationLinearMap
    ⟨P.injective_orientationLinearMap hM, P.surjective_orientationLinearMap hM⟩

@[simp] theorem orientation_ιMulti (hM : Module.rankAtStalk (R := k) M = fun _ ↦ 3)
    (x : Fin 3 → M) : P.orientation hM (exteriorPower.ιMulti k 3 x) = P.crossAlternating x :=
  P.orientationLinearMap_ιMulti x

@[simp] theorem orientationAlternating_orientation
    (hM : Module.rankAtStalk (R := k) M = fun _ ↦ 3) :
    orientationAlternating (P.orientation hM) = P.crossAlternating :=
  AlternatingMap.ext fun x ↦ P.orientation_ιMulti hM x

/-- The dual orientation `θ*⁻¹` of `GPR 22.14` induced by the orientation of a pair is the volume
form of its dual vector product. Both satisfy the determinant identity `GPR (22.14.1)` against
the same primal volume form, which takes the value `1` on some element of `⋀³ M`. -/
theorem dualOrientationAlternating_orientation
    (hM : Module.rankAtStalk (R := k) M = fun _ ↦ 3) :
    dualOrientationAlternating (P.orientation hM) = P.crossDualAlternating := by
  ext f
  obtain ⟨ω, hω⟩ := (P.orientation hM).surjective 1
  have h : (dualOrientationAlternating (P.orientation hM) f - P.crossDualAlternating f) •
      (P.orientation hM).toLinearMap = 0 := by
    ext x
    have h₁ : orientationAlternating (P.orientation hM) x *
        dualOrientationAlternating (P.orientation hM) f =
          Matrix.det (.of fun i j ↦ f i (x j)) :=
      orientationAlternating_mul_dualOrientationAlternating_apply (P.orientation hM) x f
    have h₂ := P.crossAlternating_mul_crossDualAlternating hM x f
    rw [orientationAlternating_orientation] at h₁
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.smul_apply, LinearEquiv.coe_coe,
      orientation_ιMulti, smul_eq_mul, LinearMap.zero_compAlternatingMap, zero_apply]
    linear_combination h₁ - h₂
  have := LinearMap.congr_fun h ω
  rwa [LinearMap.smul_apply, LinearEquiv.coe_coe, hω, smul_eq_mul, mul_one, LinearMap.zero_apply,
    sub_eq_zero] at this

/-- **Every vector-product pair comes from an orientation.** On a finite projective module of
constant rank three, the pair induced (`GPR 22.14`) by the orientation of a pair is the pair
itself. -/
@[simp] theorem ofOrientation_orientation (hM : Module.rankAtStalk (R := k) M = fun _ ↦ 3) :
    VectorProductPair.ofOrientation hM (P.orientation hM) = P := by
  refine VectorProductPair.ext ?_ ?_
  · ext v w x
    rw [VectorProductPair.ofOrientation_cross, crossOfOrientation_apply,
      orientationAlternating_orientation, crossAlternating_apply]
    rfl
  · ext f g
    apply (Module.evalEquiv k M).injective
    ext h
    rw [Module.evalEquiv_apply, Module.evalEquiv_apply, Module.Dual.eval_apply,
      Module.Dual.eval_apply, VectorProductPair.ofOrientation_crossDual,
      apply_crossDualOfOrientation, dualOrientationAlternating_orientation,
      crossDualAlternating_apply_cycle]

/-- The orientation of the pair induced by an orientation is the orientation itself. -/
@[simp] theorem orientation_ofOrientation (hM : Module.rankAtStalk (R := k) M = fun _ ↦ 3)
    (θ : (⋀[k]^3 M) ≃ₗ[k] k) :
    (VectorProductPair.ofOrientation hM θ).orientation hM = θ := by
  apply LinearEquiv.toLinearMap_injective
  ext x
  have hx : ![x 0, x 1, x 2] = x := by
    ext i
    fin_cases i <;> rfl
  simp [crossAlternating_apply, hx]

/-- **Orientations are vector-product pairs** (`GPR 22.14`): on a finite projective module of
constant rank three, `VectorProductPair.ofOrientation` is a bijection from orientations to
vector-product pairs, with inverse `VectorProductPair.orientation`. -/
noncomputable def orientationEquiv (hM : Module.rankAtStalk (R := k) M = fun _ ↦ 3) :
    ((⋀[k]^3 M) ≃ₗ[k] k) ≃ VectorProductPair k M where
  toFun θ := VectorProductPair.ofOrientation hM θ
  invFun P := P.orientation hM
  left_inv θ := orientation_ofOrientation hM θ
  right_inv P := P.ofOrientation_orientation hM

@[simp] theorem orientationEquiv_apply (hM : Module.rankAtStalk (R := k) M = fun _ ↦ 3)
    (θ : (⋀[k]^3 M) ≃ₗ[k] k) :
    orientationEquiv hM θ = VectorProductPair.ofOrientation hM θ := rfl

@[simp] theorem orientationEquiv_symm_apply (hM : Module.rankAtStalk (R := k) M = fun _ ↦ 3) :
    (orientationEquiv hM).symm P = P.orientation hM := rfl

end VectorProductPair

end Module

namespace ConicAlgebra.IsElementaryIdempotent

variable {k : Type u} {A : Type v} [CommRing k] [NonAssocRing A] [Module k A]
  [SMulCommClass k A A] [IsScalarTower k A A] [IsAlternative A]
  {C : ConicAlgebra k A} {c : A}

/-- The Peirce-coordinate equivalence sends the matrix unit `e₁₁` of `GPR (22.14.7)` to the
idempotent `c`. -/
theorem twistedZorEquiv_matrixUnit (hc : C.IsElementaryIdempotent c)
    (hmul : C.IsMultiplicative) (hreg : C.norm.IsGPRRegular) :
    hc.twistedZorEquiv hmul hreg
      (((1, 0), (0, 0)) : TwistedZor (hc.peirceVectorProductPair hmul hreg)) = c := by
  change peirceElement c 1 0 ((hc.offDiagonalDuality hmul hreg).symm 0) 0 = c
  simp [peirceElement]

/-- The volume form of the Peirce vector products is `(u, v, w) ↦ n_C(uv, w)`, the trilinear form
of `GPR (22.15.3)`. -/
theorem crossAlternating_peirceVectorProductPair (hc : C.IsElementaryIdempotent c)
    (hmul : C.IsMultiplicative) (hreg : C.norm.IsGPRRegular)
    (u v w : ZornTwistingModule (k := k) c) :
    (hc.peirceVectorProductPair hmul hreg).crossAlternating ![u, v, w] =
      QuadraticMap.polar C.norm ((u : A) * v) w :=
  rfl

/-- **`GPR 22.15` (Petersson), oriented form.** Let `C` be a composition algebra of constant rank
eight with an elementary idempotent `c`, and let `M = C₂₁` be its lower-left Peirce component
(finite projective of constant rank three). The trilinear form `(u, v, w) ↦ n_C(uv, w)` of
`GPR (22.15.3)` is an orientation `θ` of `M`, and the Peirce coordinates are an isomorphism
`Zor(M, θ) ≅ C` sending the matrix unit `e₁₁` to `c` (`GPR (22.15.1)`, read in the inverse
direction). -/
theorem exists_orientation_isometryEquiv_twistedZor [Module.Finite k A] [Module.Projective k A]
    (hc : C.IsElementaryIdempotent c) (hcomp : C.IsComposition.{u, v, u})
    (hA : Module.rankAtStalk (R := k) A = fun _ ↦ 8) :
    letI : Module.Finite k (ZornTwistingModule (k := k) c) :=
      IsAlternative.finite_peirceComponent true false
    letI : Module.Projective k (ZornTwistingModule (k := k) c) :=
      IsAlternative.projective_peirceComponent hc.mul_self true false
    ∃ θ : (⋀[k]^3 (ZornTwistingModule (k := k) c)) ≃ₗ[k] k,
      (∀ u v w : ZornTwistingModule (k := k) c,
        θ (exteriorPower.ιMulti k 3 ![u, v, w]) = QuadraticMap.polar C.norm ((u : A) * v) w) ∧
      ∃ e : (twistedZor (Module.VectorProductPair.ofOrientation
          (hc.rankAtStalk_twistingModule_eq_three_of_isComposition hcomp hA) θ)).norm.IsometryEquiv
          C.norm,
        e 1 = 1 ∧ (∀ x y, e (x * y) = e x * e y) ∧
          e (((1, 0), (0, 0)) : TwistedZor (Module.VectorProductPair.ofOrientation
            (hc.rankAtStalk_twistingModule_eq_three_of_isComposition hcomp hA) θ)) = c := by
  let : Module.Finite k (ZornTwistingModule (k := k) c) :=
    IsAlternative.finite_peirceComponent true false
  let : Module.Projective k (ZornTwistingModule (k := k) c) :=
    IsAlternative.projective_peirceComponent hc.mul_self true false
  let hreg := hcomp.isGPRRegular_of_rankAtStalk_ne_one hA (by omega)
  let P := hc.peirceVectorProductPair hcomp.isMultiplicative hreg
  have hM : Module.rankAtStalk (R := k) (ZornTwistingModule (k := k) c) = fun _ ↦ 3 :=
    hc.rankAtStalk_twistingModule_eq_three_of_isComposition hcomp hA
  refine ⟨P.orientation hM, fun u v w ↦ P.orientation_ιMulti hM _, ?_⟩
  rw [P.ofOrientation_orientation hM]
  exact ⟨hc.twistedZorIsometryEquiv hcomp.isMultiplicative hreg,
    hc.twistedZorEquiv_one hcomp.isMultiplicative hreg,
    hc.twistedZorEquiv_mul hcomp.isMultiplicative hreg,
    hc.twistedZorEquiv_matrixUnit hcomp.isMultiplicative hreg⟩

/-- **`GPR 22.15` (Petersson), oriented form, isomorphism only.** A reduced composition algebra of
constant rank eight is isomorphic to `Zor(M, θ)` for its lower-left Peirce component `M` and some
orientation `θ` of `M`. -/
theorem exists_orientation_isomorphic_twistedZor [Module.Finite k A] [Module.Projective k A]
    (hc : C.IsElementaryIdempotent c) (hcomp : C.IsComposition.{u, v, u})
    (hA : Module.rankAtStalk (R := k) A = fun _ ↦ 8) :
    letI : Module.Finite k (ZornTwistingModule (k := k) c) :=
      IsAlternative.finite_peirceComponent true false
    letI : Module.Projective k (ZornTwistingModule (k := k) c) :=
      IsAlternative.projective_peirceComponent hc.mul_self true false
    ∃ θ : (⋀[k]^3 (ZornTwistingModule (k := k) c)) ≃ₗ[k] k,
      (twistedZor (Module.VectorProductPair.ofOrientation
        (hc.rankAtStalk_twistingModule_eq_three_of_isComposition hcomp hA) θ)).Isomorphic C := by
  obtain ⟨θ, -, e, h₁, hmul, -⟩ := hc.exists_orientation_isometryEquiv_twistedZor hcomp hA
  exact ⟨θ, e, h₁, hmul⟩

/-- **`GPR 22.15` (Petersson), in `GPR`'s words.** Every reduced composition algebra of constant
rank eight is isomorphic to `Zor(M, θ)` for some finitely generated projective module `M` of
constant rank three and some orientation `θ` of `M`. -/
theorem exists_isomorphic_twistedZor_ofOrientation [Module.Finite k A] [Module.Projective k A]
    (hc : C.IsElementaryIdempotent c) (hcomp : C.IsComposition.{u, v, u})
    (hA : Module.rankAtStalk (R := k) A = fun _ ↦ 8) :
    ∃ (M : Type v) (_ : AddCommGroup M) (_ : Module k M) (_ : Module.Finite k M)
      (_ : Module.Projective k M) (hM : Module.rankAtStalk (R := k) M = fun _ ↦ 3)
      (θ : (⋀[k]^3 M) ≃ₗ[k] k),
        (twistedZor (Module.VectorProductPair.ofOrientation hM θ)).Isomorphic C := by
  let : Module.Finite k (ZornTwistingModule (k := k) c) :=
    IsAlternative.finite_peirceComponent true false
  let : Module.Projective k (ZornTwistingModule (k := k) c) :=
    IsAlternative.projective_peirceComponent hc.mul_self true false
  obtain ⟨θ, h⟩ := hc.exists_orientation_isomorphic_twistedZor hcomp hA
  exact ⟨ZornTwistingModule (k := k) c, inferInstance, inferInstance, inferInstance,
    inferInstance, _, θ, h⟩

end ConicAlgebra.IsElementaryIdempotent

namespace ConicAlgebra

variable {k : Type u} [CommRing k]

/-- Twisted Zorn vector matrices on a finite projective module of constant rank three have
constant rank eight: `1 + 3 + 1 + 3`. -/
theorem rankAtStalk_twistedZor {M : Type v} [AddCommGroup M] [Module k M] [Module.Finite k M]
    [Module.Projective k M] (P : Module.VectorProductPair k M)
    (hM : Module.rankAtStalk (R := k) M = fun _ ↦ 3) :
    Module.rankAtStalk (R := k) (TwistedZor P) = fun _ ↦ 8 := by
  change Module.rankAtStalk (R := k) ((k × Module.Dual k M) × (k × M)) = _
  rw [Module.rankAtStalk_prod, Module.rankAtStalk_prod, Module.rankAtStalk_prod,
    Module.rankAtStalk_dual, hM]
  ext p
  have := p.nontrivial
  simp

variable {A : Type v} [NonAssocRing A] [Module k A] [SMulCommClass k A A] [IsScalarTower k A A]
  [IsAlternative A] [Module.Finite k A] [Module.Projective k A]

/-- **`GPR 22.15` (Petersson).** Up to isomorphism, the reduced octonion algebras are precisely
the algebras `Zor(M, θ)` of twisted Zorn vector matrices, for `M` finitely generated projective of
constant rank three and `θ` an orientation of `M`. A reduced octonion algebra is expressed as a
composition algebra of constant rank eight with an elementary idempotent; by `GPR 22.7` these are
the idempotents `GPR 22.6` asks for (absolutely primitive ones) when `k ≠ 0`. The direction `→` is
`IsElementaryIdempotent.exists_isomorphic_twistedZor_ofOrientation`; the direction `←` is the
first half of `GPR 22.15`'s proof (`isComposition_twistedZor`,
`hasElementaryIdempotent_twistedZor`), together with the rank count `rankAtStalk_twistedZor`. -/
theorem exists_isomorphic_twistedZor_ofOrientation_iff (C : ConicAlgebra k A) :
    (∃ (M : Type v) (_ : AddCommGroup M) (_ : Module k M) (_ : Module.Finite k M)
        (_ : Module.Projective k M) (hM : Module.rankAtStalk (R := k) M = fun _ ↦ 3)
        (θ : (⋀[k]^3 M) ≃ₗ[k] k),
          (twistedZor (Module.VectorProductPair.ofOrientation hM θ)).Isomorphic C) ↔
      C.IsComposition.{u, v, u} ∧ C.HasElementaryIdempotent ∧
        Module.rankAtStalk (R := k) A = fun _ ↦ 8 := by
  constructor
  · rintro ⟨M, _, _, _, _, hM, θ, h⟩
    refine ⟨h.symm.isComposition isComposition_twistedZor, ?_, ?_⟩
    · exact h.hasElementaryIdempotent_iff.mp (hasElementaryIdempotent_twistedZor _)
    · obtain ⟨e, -, -⟩ := h
      rw [← Module.rankAtStalk_eq_of_equiv e.toLinearEquiv]
      exact rankAtStalk_twistedZor _ hM
  · rintro ⟨hcomp, ⟨c, hc⟩, hA⟩
    exact hc.exists_isomorphic_twistedZor_ofOrientation hcomp hA

end ConicAlgebra
