/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
import CompositionAlgebras.Nonassociative.Alternative.Defs

/-!
# The Moufang identities

In any alternative ring the three **Moufang identities** hold:

1. **left**   `a * (b * (a * c)) = ((a * b) * a) * c`
2. **right**  `((c * a) * b) * a = c * (a * (b * a))`
3. **middle** `(a * b) * (c * a) = a * ((b * c) * a)`

Modulo the flexible law (`IsAlternative.flexible`) these agree with the forms in `GPR 13.3`.

⚠ **Load-bearing for Layer 6.** `GPR 18.1` derives the Cayley–Dickson identities from the *middle*
Moufang identity together with the linearized left alternative law
(`IsAlternative.left_alt_linearized`). Both must remain available in exactly these shapes; if you
restate them, check `Conic/CayleyDickson.lean` still elaborates.

## Implementation notes

`left_moufang` is obtained from `right_moufang` by transport along `MulOpposite`, using the
`IsAlternative αᵐᵒᵖ` instance from `Defs.lean`.

⚠ **TODO (proof hygiene).** `right_moufang` is closed by `grind`, and in the original development
this required `set_option maxHeartbeats 32000000` — 160× the default. That is a symptom of brute
force, not a proof. Replace it with structured `calc` reasoning from the linearized laws before
this goes anywhere near mathlib; see `AGENTS.md` §7. The heartbeat bound below is a deliberate,
much smaller placeholder and may need raising until that proof is rewritten.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 13.2, 13.3.
* Schafer, *An Introduction to Nonassociative Algebras*, §3.
* Zhevlakov et al., *Rings That Are Nearly Associative*, Ch. 2.
-/

universe u

namespace IsAlternative

variable {α : Type u} [NonUnitalNonAssocRing α] [IsAlternative α]

set_option maxHeartbeats 1000000 in
-- The final `grind` call currently exceeds the default heartbeat budget.
/-- **Right Moufang identity**: `((c * a) * b) * a = c * (a * (b * a))`.

The enlarged heartbeat budget is local to this proof while its final `grind` call remains. -/
theorem right_moufang (a b c : α) :
    ((c * a) * b) * a = c * (a * (b * a)) := by
  have hA := left_alt_linearized (c * a) b a
  have hB := right_alt_linearized c a (b * a)
  have h3 := mul_self_mul_right a c
  have h4 := mul_self_mul_right a b
  have hD := left_alt_linearized c b a
  have h6a := mul_self_mul_right a (c * b)
  have h6b := mul_self_mul_right a (b * c)
  have hF := left_alt_linearized c b (a * a)
  have hE : (c * (b * a)) * a + (b * (c * a)) * a =
            ((c * b) * a) * a + ((b * c) * a) * a := by
    have := congr_arg (· * a) hD; simp only [add_mul] at this; exact this
  grind

/-- **Left Moufang identity**: `a * (b * (a * c)) = ((a * b) * a) * c`.

Proved by applying `right_moufang` in the opposite ring. -/
theorem left_moufang (a b c : α) :
    a * (b * (a * c)) = ((a * b) * a) * c := by
  have h := right_moufang (MulOpposite.op a) (MulOpposite.op b) (MulOpposite.op c)
  simp only [← MulOpposite.op_mul] at h
  exact MulOpposite.op_injective h

/-- **Middle Moufang identity**: `(a * b) * (c * a) = a * ((b * c) * a)`.

This is the form consumed by `GPR 18.1` in the Cayley–Dickson construction. -/
theorem middle_moufang (a b c : α) :
    (a * b) * (c * a) = a * ((b * c) * a) := by
  -- Cyclic form of the alternating property.
  have h_cyclic : ∀ x y z : α,
      (y * z) * x - y * (z * x) = (z * x) * y - z * (x * y) := by
    intro x y z
    change associator y z x = associator z x y
    calc
      associator y z x = -associator y x z := associator_swap_right y z x
      _ = associator x y z := by
        rw [associator_swap_left y x z, neg_neg]
      _ = -associator x z y := associator_swap_right x y z
      _ = associator z x y := (associator_swap_left z x y).symm
  have h_linearized := right_alt_linearized a b (c * a)
  have h_extra : (a * (c * a)) * b = a * (c * (a * b)) := by
    calc
      (a * (c * a)) * b = ((a * c) * a) * b :=
        congrArg (· * b) (flexible a c).symm
      _ = a * (c * (a * b)) := (left_moufang a c b).symm
  rw [h_extra] at h_linearized
  have h_cyclic_mul := congrArg (a * ·) (h_cyclic a b c)
  simp only [mul_sub] at h_cyclic_mul
  calc
    (a * b) * (c * a) =
        a * (b * (c * a)) + a * ((c * a) * b) - a * (c * (a * b)) := by
      calc
        (a * b) * (c * a) =
            (a * b) * (c * a) + a * (c * (a * b)) - a * (c * (a * b)) := by
          abel
        _ = (a * (b * (c * a)) + a * ((c * a) * b)) - a * (c * (a * b)) := by
          rw [h_linearized]
    _ = a * ((b * c) * a) := by
      calc
        a * (b * (c * a)) + a * ((c * a) * b) - a * (c * (a * b)) =
            a * (b * (c * a)) +
              (a * ((c * a) * b) - a * (c * (a * b))) := by abel
        _ = a * (b * (c * a)) +
              (a * ((b * c) * a) - a * (b * (c * a))) := by
          rw [h_cyclic_mul]
        _ = a * ((b * c) * a) := by abel

end IsAlternative
