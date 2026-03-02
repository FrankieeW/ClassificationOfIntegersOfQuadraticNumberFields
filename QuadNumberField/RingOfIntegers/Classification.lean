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
- [ ] Non-`1 mod 4` branch theorem:
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
