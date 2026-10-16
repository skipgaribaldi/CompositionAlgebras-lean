/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import CompositionAlgebras.LGRing.ConstantRank
public import CompositionAlgebras.Module.AlternatingBaseChange
public import CompositionAlgebras.Module.VectorProduct
public import CompositionAlgebras.QuadraticForm.Regularity
public import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Oriented rank-three projective modules (`GPR 22.14`)

An orientation `θ : ⋀³ M ≃ k` of a finite projective module of constant rank three induces
the two associated vector products used to define twisted Zorn vector matrices. To prove
Binet–Cauchy over an arbitrary commutative ring, we localize at each maximal ideal. The localized
module is free of rank three, while base change for projective duals identifies its dual with the
localized dual. The primal and dual volume coefficients multiply to one by the determinant
identity from `GPR 21.7`; the based calculation then applies. Descent from all maximal
localizations proves the global identity.

## Main definitions

* `Module.VectorProductPair.ofOrientation` : the pair of associated vector products induced by
  an orientation of a constant-rank-three finite projective module.
* `Module.VectorProductPair.ofOrientationOfIsLGRing` : compatibility alias for the earlier
  LG-ring API.

## References

* [GPR] Skip Garibaldi, Holger Petersson, and Michel Racine, *Albert Algebras over Commutative
  Rings*, 9.15, 21.7, 22.14.
-/

@[expose] public section

universe u v

namespace Module

variable {k : Type u} {M : Type v} [CommRing k] [AddCommGroup M] [Module k M]
  [Module.Finite k M] [Module.Projective k M]

theorem cross_apply_crossDual_of_orientation
    (hM : Module.rankAtStalk (R := k) M = fun _ ↦ 3)
    (theta : (⋀[k]^3 M) ≃ₗ[k] k) (v w : M) (f g : Module.Dual k M) :
    crossOfOrientation theta v w (crossDualOfOrientation theta f g) =
      f v * g w - f w * g v := by
  apply sub_eq_zero.mp
  apply eq_zero_of_localization
  intro J hJ
  let S := Localization.AtPrime J
  let MS := TensorProduct k S M
  let e : TensorProduct k S (Module.Dual k M) ≃ₗ[S] Module.Dual S MS :=
    Module.Dual.baseChangeEquivOfProjective (R := k) (M := M) (A := S)
  let A : MS [⋀^Fin 3]→ₗ[S] S :=
    AlternatingMap.baseChangeAlternatingFinThree (S := S) (orientationAlternating theta)
  let D : TensorProduct k S (Module.Dual k M) [⋀^Fin 3]→ₗ[S] S :=
    AlternatingMap.baseChangeAlternatingFinThree (S := S)
      (dualOrientationAlternating theta)
  let Dt : Module.Dual S MS [⋀^Fin 3]→ₗ[S] S :=
    D.compLinearMap e.symm.toLinearMap
  let : Module.Free S MS := Module.free_of_flat_of_isLocalRing
  have hfin : Module.finrank S MS = 3 := by
    have h := congrFun hM ⟨J, hJ.isPrime⟩
    rw [Module.rankAtStalk_eq_finrank_tensorProduct] at h
    simpa [S, MS] using h
  let b : Module.Basis (Fin 3) S MS := Module.finBasisOfFinrankEq S MS hfin
  let P : VectorProductPair S MS := VectorProductPair.ofBasis b
  let vS : MS := 1 ⊗ₜ[k] v
  let wS : MS := 1 ⊗ₜ[k] w
  let fS : Module.Dual S MS := e (1 ⊗ₜ[k] f)
  let gS : Module.Dual S MS := e (1 ⊗ₜ[k] g)
  let a : S := A b
  let d : S := Dt b.dualBasis
  have he (r s : S) (q : Module.Dual k M) (x : M) :
      e (r ⊗ₜ[k] q) (s ⊗ₜ[k] x) = r * s * algebraMap k S (q x) :=
    Module.Dual.baseChangeTensor_tmul r q s x
  have had : a * d = 1 := by
    have h := AlternatingMap.baseChangeFinThree_mul_eq_det
      (S := S) (orientationAlternating theta) (dualOrientationAlternating theta) e he
      (orientationAlternating_mul_dualOrientationAlternating_apply theta)
      (b 0) (b 1) (b 2) (e.symm (b.dualBasis 0))
      (e.symm (b.dualBasis 1)) (e.symm (b.dualBasis 2))
    change a * d = 1
    simpa [a, d, A, D, Dt, AlternatingMap.baseChangeAlternatingFinThree,
      Matrix.det_fin_three] using h
  have hcross (x : MS) :
      e (1 ⊗ₜ[k] crossOfOrientation theta v w) x =
        AlternatingMap.baseChangeFinThree (S := S) (orientationAlternating theta)
          vS wS x := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp [hx, hy]
    | tmul s x =>
      rw [AlternatingMap.baseChangeFinThree_tmul]
      simp [he, crossOfOrientation_apply]
  have hcrossEq : e (1 ⊗ₜ[k] crossOfOrientation theta v w) =
      a • P.cross vS wS := by
    apply LinearMap.ext
    intro x
    rw [hcross]
    change A ![vS, wS, x] = _
    have h := DFunLike.congr_fun (A.eq_smul_basis_det b) ![vS, wS, x]
    rw [← VectorProductPair.crossAlternating_ofBasis b] at h
    simpa [a, P] using h
  have hcrossDual (h : Module.Dual S MS) :
      h (1 ⊗ₜ[k] crossDualOfOrientation theta f g) = Dt ![fS, gS, h] := by
    let q := e.symm h
    rw [← e.apply_symm_apply h]
    simp only [Dt, D, fS, gS, AlternatingMap.compLinearMap_apply,
      AlternatingMap.baseChangeAlternatingFinThree]
    have hvec : (fun i ↦ e.symm
        (![e (1 ⊗ₜ[k] f), e (1 ⊗ₜ[k] g), e (e.symm h)] i)) =
        ![(1 ⊗ₜ[k] f), (1 ⊗ₜ[k] g), q] := by
      ext i
      fin_cases i <;> simp [q]
    change e (e.symm h) (1 ⊗ₜ[k] crossDualOfOrientation theta f g) =
      AlternatingMap.baseChangeAlternatingFinThree (S := S)
        (dualOrientationAlternating theta)
        (fun i ↦ e.symm (![e (1 ⊗ₜ[k] f), e (1 ⊗ₜ[k] g), e (e.symm h)] i))
    rw [hvec]
    change e q (1 ⊗ₜ[k] crossDualOfOrientation theta f g) =
      AlternatingMap.baseChangeFinThree (S := S) (dualOrientationAlternating theta)
        (1 ⊗ₜ[k] f) (1 ⊗ₜ[k] g) q
    induction q using TensorProduct.inductionOn with
    | add x y hx hy => simp [hx, hy]
    | tmul r q =>
      rw [AlternatingMap.baseChangeFinThree_tmul]
      simp [he, apply_crossDualOfOrientation]
  have hcrossDualEq : (1 ⊗ₜ[k] crossDualOfOrientation theta f g : MS) =
      d • P.crossDual fS gS := by
    apply (Module.evalEquiv S MS).injective
    ext h
    simp only [Module.evalEquiv_apply, Module.Dual.eval_apply]
    rw [hcrossDual]
    rw [← alternating_fin_three_cycle Dt h fS gS]
    have hdet := DFunLike.congr_fun (Dt.eq_smul_basis_det b.dualBasis) ![h, fS, gS]
    rw [← VectorProductPair.crossDualAlternating_ofBasis b] at hdet
    simpa [d, P] using hdet
  have hleft : algebraMap k S
      (crossOfOrientation theta v w (crossDualOfOrientation theta f g)) =
      e (1 ⊗ₜ[k] crossOfOrientation theta v w)
        (1 ⊗ₜ[k] crossDualOfOrientation theta f g) := by
    symm
    simpa using he 1 1 (crossOfOrientation theta v w)
      (crossDualOfOrientation theta f g)
  rw [map_sub, map_sub, map_mul, map_mul, hleft, hcrossEq, hcrossDualEq]
  simp only [LinearMap.smul_apply, smul_eq_mul, map_smul]
  rw [← mul_assoc, mul_comm d a, had, one_mul]
  rw [P.cross_apply_crossDual]
  simp [fS, gS, vS, wS, he]
  ring

/-- **`GPR 22.14`.** An orientation of a finite projective module of constant rank three over an
arbitrary commutative ring induces its pair of associated vector products. -/
noncomputable def VectorProductPair.ofOrientation
    (hM : Module.rankAtStalk (R := k) M = fun _ ↦ 3)
    (theta : (⋀[k]^3 M) ≃ₗ[k] k) : VectorProductPair k M where
  cross := crossOfOrientation theta
  crossDual := crossDualOfOrientation theta
  cross_self v := by
    apply LinearMap.ext
    intro w
    rw [crossOfOrientation_apply]
    exact (orientationAlternating theta).map_eq_zero_of_eq ![v, v, w]
      (by rfl) (show (0 : Fin 3) ≠ 1 by decide)
  crossDual_self f := by
    apply (Module.evalEquiv k M).injective
    ext h
    simp only [Module.evalEquiv_apply, Module.Dual.eval_apply, map_zero]
    rw [apply_crossDualOfOrientation]
    exact (dualOrientationAlternating theta).map_eq_zero_of_eq ![f, f, h]
      (by rfl) (show (0 : Fin 3) ≠ 1 by decide)
  cross_apply_left v w := by
    rw [crossOfOrientation_apply]
    exact (orientationAlternating theta).map_eq_zero_of_eq ![v, w, v]
      (by rfl) (show (0 : Fin 3) ≠ 2 by decide)
  apply_crossDual_left f g := by
    rw [apply_crossDualOfOrientation]
    exact (dualOrientationAlternating theta).map_eq_zero_of_eq ![f, g, f]
      (by rfl) (show (0 : Fin 3) ≠ 2 by decide)
  cross_apply_crossDual := cross_apply_crossDual_of_orientation hM theta

@[simp] theorem VectorProductPair.ofOrientation_cross
    (hM : Module.rankAtStalk (R := k) M = fun _ ↦ 3)
    (theta : (⋀[k]^3 M) ≃ₗ[k] k) :
    (VectorProductPair.ofOrientation hM theta).cross = crossOfOrientation theta := rfl

@[simp] theorem VectorProductPair.ofOrientation_crossDual
    (hM : Module.rankAtStalk (R := k) M = fun _ ↦ 3)
    (theta : (⋀[k]^3 M) ≃ₗ[k] k) :
    (VectorProductPair.ofOrientation hM theta).crossDual =
      crossDualOfOrientation theta := rfl

/-- Compatibility alias for the former LG-ring-specific orientation construction. The
construction now works over every commutative ring by `VectorProductPair.ofOrientation`. -/
noncomputable def VectorProductPair.ofOrientationOfIsLGRing
    (_hLG : IsLGRing k) (hM : Module.rankAtStalk (R := k) M = fun _ ↦ 3)
    (theta : (⋀[k]^3 M) ≃ₗ[k] k) : VectorProductPair k M :=
  VectorProductPair.ofOrientation hM theta

@[simp] theorem VectorProductPair.ofOrientationOfIsLGRing_cross
    (hLG : IsLGRing k) (hM : Module.rankAtStalk (R := k) M = fun _ ↦ 3)
    (theta : (⋀[k]^3 M) ≃ₗ[k] k) :
    (VectorProductPair.ofOrientationOfIsLGRing hLG hM theta).cross =
      crossOfOrientation theta := rfl

@[simp] theorem VectorProductPair.ofOrientationOfIsLGRing_crossDual
    (hLG : IsLGRing k) (hM : Module.rankAtStalk (R := k) M = fun _ ↦ 3)
    (theta : (⋀[k]^3 M) ≃ₗ[k] k) :
    (VectorProductPair.ofOrientationOfIsLGRing hLG hM theta).crossDual =
      crossDualOfOrientation theta := rfl

end Module
