/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import CompositionAlgebras.Composition.Fields.Basic
public import CompositionAlgebras.Composition.Tower

/-!
# Splitting over the fraction field (`GPR 22.19(i)`)

Let `k` be a principal ideal domain with field of fractions `F`, and `C` a composition algebra of
rank `r > 1` over `k`. `GPR 22.19` lists five equivalent conditions:

(i) `C_F` is split; (ii) the norm of `C` is isotropic in the sense of `GPR 11.17`; (iii) the norm
of `C` represents zero in the sense of `GPR Exc. 12.38`; (iv) `C` has zero divisors; (v) `C` is
split.

Conditions (ii)–(v) are proved equivalent in `Composition/Reduced/Classification.lean`. This file
adds condition (i), following the proof of `GPR 22.19`: (i) is linked to (iii) by anisotropy.

**Anisotropy descends from the fraction field** (`GPR Exc. 12.38(b)`, for quadratic forms). A
quadratic form on a finitely generated projective `k`-module represents zero if and only if its
extension to a localization at non-zero-divisors does. A nonzero null vector `m` stays nonzero as
`1 ⊗ m`, because projective modules have no torsion; conversely, clearing denominators turns a
nonzero null vector of the extension into `1 ⊗ m` for a nonzero null vector `m`.

Over the field `F`, splitness of `C_F` is failure of anisotropy of its norm (`GPR 22.18`), so (i)
is equivalent to (iii); the remaining conditions follow from the results over a PID.

## Main results

* `QuadraticForm.anisotropic_baseChangeOfProjective_iff_of_isLocalization` : **`GPR Exc. 12.38(b)`**
  for quadratic forms on finitely generated projective modules.
* `QuadraticForm.anisotropic_baseChangeOfProjective_iff_of_isFractionRing` : the case of the
  fraction field.
* `ConicAlgebra.IsComposition.isSplitOfRank_baseChangeOfProjective_iff_not_anisotropic` :
  **`GPR 22.19`, (i) ↔ (iii)**, over any ring with a fraction field.
* `ConicAlgebra.IsComposition.isSplitOfRank_baseChangeOfProjective_iff_not_noZeroDivisors` :
  **`GPR 22.19`, (i) ↔ (iv)**, over an integral domain.
* `ConicAlgebra.IsComposition.isSplitOfRank_baseChangeOfProjective_iff_isGPRIsotropic_of_pid` :
  **`GPR 22.19`, (i) ↔ (ii)**, over a PID.
* `ConicAlgebra.IsComposition.isSplitOfRank_baseChangeOfProjective_iff_of_pid` :
  **`GPR 22.19`, (i) ↔ (v)**, over a PID.

## Implementation notes

The fraction field is any field `F` with `[IsFractionRing k F]`, not only `FractionRing k`. It lives
in the universe of `k`, because the field form of `GPR 22.18` and the results over a PID are stated
for `C.IsComposition.{u, v, u}`: the non-singularity of the norm quantifies over fields in the
universe of the base.

⚠ **Only the PID results use the PID.** The equivalences (i) ↔ (iii) and (i) ↔ (iv) hold over any
integral domain, and are stated that way. The step from (iii) to (ii) is `GPR Exc. 12.38(c)`, and
the step from (ii) to (v) uses that projective modules over a PID are free; neither generalizes to
arbitrary domains. `GPR` remarks after `22.19` that (i) ↔ (v) holds over some other classes of
domains, and that over finitely generated algebras over a field the answer depends on the number of
generators.

⚠ **Rank one is excluded**, as in `GPR 22.19`: the rank-one algebra `k` is split, while its norm
`x ↦ x²` is anisotropic over a domain.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 11.17,
  Exc. 12.38, 22.18, 22.19.
-/

@[expose] public section

universe u v w

open scoped TensorProduct nonZeroDivisors

namespace QuadraticForm

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  [Module.Finite R M] [Module.Projective R M]

/-- **`GPR Exc. 12.38(b)`, for quadratic forms.** Let `L` be the localization of `R` at a
multiplicative set `S` of non-zero-divisors. A quadratic form on a finitely generated projective
`R`-module is anisotropic if and only if its base change to `L` is; equivalently, it represents
zero if and only if its base change does.

A null vector `m ≠ 0` gives the null vector `1 ⊗ m ≠ 0`, since a projective module has no
`S`-torsion. Conversely a null vector `x` of `L ⊗[R] M` satisfies `s • x = 1 ⊗ m` for some `s ∈ S`
and `m ∈ M`, and then `Q m` maps to `s² Q_L(x) = 0`. -/
theorem anisotropic_baseChangeOfProjective_iff_of_isLocalization (S : Submonoid R) (hS : S ≤ R⁰)
    (L : Type w) [CommRing L] [Algebra R L] [IsLocalization S L] (Q : QuadraticForm R M) :
    (Q.baseChangeOfProjective L).Anisotropic ↔ Q.Anisotropic := by
  have hval (m : M) :
      Q.baseChangeOfProjective L (TensorProduct.mk R L M 1 m) = algebraMap R L (Q m) := by
    rw [TensorProduct.mk_apply, baseChangeOfProjective_tmul, mul_one, Algebra.smul_def, mul_one]
  refine ⟨fun h m hm ↦ ?_, fun h x hx ↦ ?_⟩
  · obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff S (TensorProduct.mk R L M 1)).mp <|
      h _ (by rw [hval, hm, map_zero])
    exact Module.Flat.isSMulRegular_of_nonZeroDivisors (hS s.2) (hs.trans (smul_zero _).symm)
  · obtain ⟨⟨m, s⟩, hms⟩ := IsLocalizedModule.surj S (TensorProduct.mk R L M 1) x
    rw [Submonoid.smul_def, ← algebraMap_smul L] at hms
    have hm : m = 0 := h m <| IsLocalization.injective L hS <| by
      rw [map_zero, ← hval, ← hms, QuadraticMap.map_smul, hx, smul_zero]
    rw [hm, map_zero] at hms
    exact (IsLocalization.map_units L s).smul_eq_zero.mp hms

/-- **`GPR Exc. 12.38(b)` over the fraction field.** A quadratic form on a finitely generated
projective module is anisotropic if and only if its base change to the fraction field is. -/
theorem anisotropic_baseChangeOfProjective_iff_of_isFractionRing (F : Type w) [CommRing F]
    [Algebra R F] [IsFractionRing R F] (Q : QuadraticForm R M) :
    (Q.baseChangeOfProjective F).Anisotropic ↔ Q.Anisotropic :=
  anisotropic_baseChangeOfProjective_iff_of_isLocalization R⁰ le_rfl F Q

end QuadraticForm

namespace ConicAlgebra.IsComposition

variable {k : Type u} {A : Type v} [CommRing k] [NonAssocRing A] [Module k A]
  [SMulCommClass k A A] [IsScalarTower k A A] [Module.Finite k A] [Module.Projective k A]
  {C : ConicAlgebra k A} {r : ℕ} (F : Type u) [Field F] [Algebra k F] [IsFractionRing k F]

/-- **`GPR 22.19`, (i) ↔ (iii).** A composition algebra of constant rank `2`, `4`, or `8` is split
after extension to the fraction field if and only if its norm represents zero.

This is the first step of the proof of `GPR 22.19`: over the field `F` it is `GPR 22.18`, and the
norm of `C_F` represents zero exactly when the norm of `C` does (`GPR Exc. 12.38(b)`). It needs
neither the PID hypothesis of `GPR 22.19` nor any hypothesis on the base beyond the existence of a
fraction field. -/
theorem isSplitOfRank_baseChangeOfProjective_iff_not_anisotropic
    (hcomp : C.IsComposition.{u, v, u}) (hA : Module.rankAtStalk (R := k) A = fun _ ↦ r)
    (hr : r = 2 ∨ r = 4 ∨ r = 8) :
    (C.baseChangeOfProjective F).IsSplitOfRank r ↔ ¬ C.norm.Anisotropic := by
  rw [(hcomp.baseChangeOfProjective F).isSplitOfRank_iff_not_anisotropic
      (Module.finrank_baseChange_of_rankAtStalk_eq hA F) hr, baseChangeOfProjective_norm,
    QuadraticForm.anisotropic_baseChangeOfProjective_iff_of_isFractionRing]

/-- **`GPR 22.19`, (i) ↔ (iv).** Over an integral domain, a composition algebra of constant rank
`2`, `4`, or `8` is split after extension to the fraction field if and only if it has zero
divisors, expressed as the negation of mathlib's `NoZeroDivisors`. -/
theorem isSplitOfRank_baseChangeOfProjective_iff_not_noZeroDivisors [IsDomain k]
    (hcomp : C.IsComposition.{u, v, u}) (hA : Module.rankAtStalk (R := k) A = fun _ ↦ r)
    (hr : r = 2 ∨ r = 4 ∨ r = 8) :
    (C.baseChangeOfProjective F).IsSplitOfRank r ↔ ¬ NoZeroDivisors A :=
  (hcomp.isSplitOfRank_baseChangeOfProjective_iff_not_anisotropic F hA hr).trans
    (not_congr hcomp.isMultiplicative.anisotropic_iff_noZeroDivisors_of_isDomain)

/-- **`GPR 22.19`, (i) ↔ (ii).** Over a PID, a composition algebra of constant rank `2`, `4`, or
`8` is split after extension to the fraction field if and only if its norm is isotropic in the sense
of `GPR 11.17`, i.e. has a unimodular null vector. The step from a nonzero null vector to a
unimodular one is `GPR Exc. 12.38(c)`. -/
theorem isSplitOfRank_baseChangeOfProjective_iff_isGPRIsotropic_of_pid [IsDomain k]
    [IsPrincipalIdealRing k] (hcomp : C.IsComposition.{u, v, u})
    (hA : Module.rankAtStalk (R := k) A = fun _ ↦ r) (hr : r = 2 ∨ r = 4 ∨ r = 8) :
    (C.baseChangeOfProjective F).IsSplitOfRank r ↔ C.norm.IsGPRIsotropic :=
  (hcomp.isSplitOfRank_baseChangeOfProjective_iff_not_anisotropic F hA hr).trans
    QuadraticMap.isGPRIsotropic_iff_not_anisotropic_of_pid.symm

/-- **`GPR 22.19`, (i) ↔ (v).** Over a PID with fraction field `F`, a composition algebra of
constant rank `2`, `4`, or `8` is split if and only if it becomes split over `F`.

Both directions pass through condition (iii), the norm representing zero: (i) ↔ (iii) is
`isSplitOfRank_baseChangeOfProjective_iff_not_anisotropic`, and (iii) ↔ (v) over a PID is
`isSplitOfRank_iff_not_anisotropic_of_pid`. -/
theorem isSplitOfRank_baseChangeOfProjective_iff_of_pid [IsDomain k] [IsPrincipalIdealRing k]
    (hcomp : C.IsComposition.{u, v, u}) (hA : Module.rankAtStalk (R := k) A = fun _ ↦ r)
    (hr : r = 2 ∨ r = 4 ∨ r = 8) :
    (C.baseChangeOfProjective F).IsSplitOfRank r ↔ C.IsSplitOfRank r :=
  (hcomp.isSplitOfRank_baseChangeOfProjective_iff_not_anisotropic F hA hr).trans
    (hcomp.isSplitOfRank_iff_not_anisotropic_of_pid hA hr).symm

end ConicAlgebra.IsComposition
