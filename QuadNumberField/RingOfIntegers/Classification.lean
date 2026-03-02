/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadNumberField.RingOfIntegers.Integrality
import QuadNumberField.RingOfIntegers.ModFour
import QuadNumberField.RingOfIntegers.ZOnePlusSqrtOverTwo

/-!
# Ring Of Integers Classification

This file should contain the final classification theorem for
`𝓞 (QuadNumberField d)`.

## TODO (Revised for Final Classification)

1. Lock target theorem signatures (per current project goal)
- [x] Non-`1 mod 4` branch theorem:
  `ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one
    (d : ℤ) [QuadFieldParam d] [NumberField (QuadNumberField d)]
    (hd4 : d % 4 ≠ 1) :
    Nonempty (𝓞 (QuadNumberField d) ≃+* Zsqrtd d)`.
- [ ] `1 mod 4` branch theorem (with explicit parameter extraction):
  `ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one
    (d : ℤ) [QuadFieldParam d] [NumberField (QuadNumberField d)]
    (hd4 : d % 4 = 1) :
    ∃ k : ℤ, d = 1 + 4 * k ∧
      Nonempty (𝓞 (QuadNumberField d) ≃+* ZOnePlusSqrtOverTwo k)`.
- [ ] Final classification theorem combining the two branch theorems.

2. Dependency order from supporting files
- [ ] `ModFour.lean`: produce `k` from `d % 4 = 1` and branch split lemmas.
- [ ] `HalfInt.lean`: provide trace/norm formulas and parity normal form.
- [ ] `Integrality.lean`: supply integral-closure transfer into branch targets.
- [ ] `Zsqrtd.lean` / `ZOnePlusSqrtOverTwo.lean`: expose branch target APIs.

3. Acceptance checks (from PDF + old draft)
- [ ] Non-`1 mod 4` branch matches `𝓞 = ℤ[√d]`.
- [ ] `1 mod 4` branch matches `𝓞 = ℤ[(1 + √d)/2]`, represented via `d = 1 + 4*k`.
- [ ] No theorem-statement drift from the locked signatures above.
-/

open scoped NumberField

namespace QuadNumberField
namespace RingOfIntegers
namespace ClassificationAPI

/-- API re-export for the non-`1 mod 4` branch.

The full proof intentionally lives in `Integrality.lean` because it is an
integral-closure construction argument.
This wrapper keeps `Classification.lean` as the classification-entry layer
without duplicating technical proof details. -/
theorem ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one
    (d : ℤ) [QuadFieldParam d] [NumberField (QuadNumberField d)]
    (hd4 : d % 4 ≠ 1) :
    Nonempty (𝓞 (QuadNumberField d) ≃+* Zsqrtd d) := by
  exact QuadNumberField.RingOfIntegers.ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one d hd4

/-- API re-export for the arithmetic bridge in the `d = 1 + 4k` branch.

The proof is in `Integrality.lean`; this theorem keeps branch-facing access in
`Classification.lean` without duplicating internals. -/
theorem dvd_four_sub_sq_iff_exists_zOnePlusSqrtOverTwo_image_of_one_mod_four
      (k a' b' : ℤ) (hd : Squarefree (1 + 4 * k)) :
      4 ∣ (a' ^ 2 - (1 + 4 * k) * b' ^ 2) ↔
        ∃ z : ZOnePlusSqrtOverTwo k,
        ZOnePlusSqrtOverTwo.toQsqrtdFun k z =
          QuadNumberField.RingOfIntegers.halfInt (1 + 4 * k) a' b' := by
  exact RingOfIntegers.dvd_four_sub_sq_iff_exists_zOnePlusSqrtOverTwo_image_of_one_mod_four
    k a' b' hd

end ClassificationAPI
end RingOfIntegers
end QuadNumberField
