/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
import Mathlib.Algebra.Algebra.NonUnitalSubalgebra

/-!
# Unital subalgebras of non-associative algebras

Mathlib's `Subalgebra` requires an associative `Semiring`, while its
`NonUnitalSubalgebra` works for a `NonUnitalNonAssocSemiring`. Composition algebras are unital but
need not be associative, so neither object alone represents their unital subalgebras. This file
adds the missing one-field wrapper.

## Main definitions

* `NonAssocSubalgebra R A` : a mathlib `NonUnitalSubalgebra R A` containing `1`.

## Implementation notes

⚠ This is deliberately not named `Subalgebra`: mathlib owns that name for associative algebras.
The underlying multiplication and scalar-action API is inherited from
`NonUnitalSubalgebra`; only the unit and its laws are new.
-/

universe u v

/-- A unital subalgebra of a possibly non-associative algebra. -/
structure NonAssocSubalgebra (R : Type u) (A : Type v) [CommRing R]
    [NonAssocRing A] [Module R A] extends NonUnitalSubalgebra R A where
  /-- The ambient unit belongs to the subalgebra. -/
  one_mem : (1 : A) ∈ carrier

namespace NonAssocSubalgebra

variable {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]

instance : SetLike (NonAssocSubalgebra R A) A where
  coe S := S.carrier
  coe_injective S T h := by
    cases S with
    | mk S hS =>
      cases T with
      | mk T hT =>
        have : S = T := NonUnitalSubalgebra.ext fun x ↦ Set.ext_iff.mp h x
        subst T
        rfl

instance : NonUnitalSubsemiringClass (NonAssocSubalgebra R A) A where
  zero_mem {s} := s.toNonUnitalSubalgebra.zero_mem
  add_mem {s} := s.toNonUnitalSubalgebra.add_mem
  mul_mem {s} := s.toNonUnitalSubalgebra.mul_mem

instance : SMulMemClass (NonAssocSubalgebra R A) R A where
  smul_mem {s} r {_} hx := s.toNonUnitalSubalgebra.smul_mem r hx

instance : NegMemClass (NonAssocSubalgebra R A) A where
  neg_mem {s} {_} hx := s.toNonUnitalSubalgebra.neg_mem hx

instance : NonUnitalSubringClass (NonAssocSubalgebra R A) A where

instance (S : NonAssocSubalgebra R A) : One S := ⟨⟨1, S.one_mem⟩⟩

@[simp, norm_cast] theorem coe_one (S : NonAssocSubalgebra R A) : ((1 : S) : A) = 1 := rfl

instance (S : NonAssocSubalgebra R A) : NatCast S := ⟨Nat.unaryCast⟩

instance (S : NonAssocSubalgebra R A) : IntCast S := ⟨Int.castDef⟩

instance (S : NonAssocSubalgebra R A) : NonAssocRing S :=
  NonAssocRing.mk (fun x ↦ Subtype.ext (by exact one_mul (x : A)))
    (fun x ↦ Subtype.ext (by exact mul_one (x : A)))

end NonAssocSubalgebra
