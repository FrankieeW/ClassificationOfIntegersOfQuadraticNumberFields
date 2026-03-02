/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadNumberField.RingOfIntegers.HalfInt
import QuadNumberField.RingOfIntegers.ModFour

/-!
# `Integrality` Layer

This file is for integrality criteria in `QuadNumberField d`, mainly via trace
and norm identities.

## TODO (Revised)

1. Integrality normal form (port/adapt from old `ZQuadPath`)
- [ ] Prove: integral `x` in `Qsqrtd (d : ℚ)` has half-integer coordinates.
- [ ] Derive `4 ∣ (a'^2 - d * b'^2)` for those half-integer coordinates.
- [ ] Provide a reusable wrapper theorem under `[QuadFieldParam d]`.

2. Non-`1 mod 4` branch closure model
- [ ] Build `IsIntegralClosure (Zsqrtd d) ℤ (QuadNumberField d)` under `d % 4 ≠ 1`.
- [ ] Deduce `Nonempty (𝓞 (QuadNumberField d) ≃+* Zsqrtd d)`.
- [ ] Keep theorem names aligned with `Classification.lean`.

3. `1 mod 4` branch closure model
- [ ] Build `IsIntegralClosure (ZOnePlusSqrtOverTwo k) ℤ (Qsqrtd ((1 + 4 * k : ℤ) : ℚ))`.
- [ ] Transport from `d = 1 + 4 * k` to a theorem about `QuadNumberField d`.
- [ ] Deduce `Nonempty (𝓞 (QuadNumberField d) ≃+* ZOnePlusSqrtOverTwo k)`.
-/

namespace QuadNumberField
namespace RingOfIntegers

open scoped NumberField

/-- In the non-`1 mod 4` branch, divisibility by `4` is equivalent to representability
in the image of `Zsqrtd d` under the canonical embedding into `Q(√d)`. -/
theorem dvd_four_sub_sq_iff_exists_zsqrtd_image_of_ne_one_mod_four
    (d a' b' : ℤ) (hd : Squarefree d) (hd4 : d % 4 ≠ 1) :
    4 ∣ (a' ^ 2 - d * b' ^ 2) ↔
      ∃ z : Zsqrtd d, Zsqrtd.toQsqrtdHom d z = Zsqrtd.halfInt (d := d) a' b' := by
  rw [dvd_four_sub_sq_iff_even_even_of_ne_one_mod_four d a' b' hd hd4]
  simpa using (Zsqrtd.halfInt_mem_range_toQsqrtdHom_iff_even_even d a' b')

/-- Forward direction in the non-`1 mod 4` branch. -/
theorem exists_zsqrtd_image_of_dvd_four_sub_sq_of_ne_one_mod_four
    (d a' b' : ℤ) (hd : Squarefree d) (hd4 : d % 4 ≠ 1)
    (hdiv : 4 ∣ (a' ^ 2 - d * b' ^ 2)) :
    ∃ z : Zsqrtd d, Zsqrtd.toQsqrtdHom d z = Zsqrtd.halfInt (d := d) a' b' :=
  (dvd_four_sub_sq_iff_exists_zsqrtd_image_of_ne_one_mod_four d a' b' hd hd4).1 hdiv

/-- Reverse direction in the non-`1 mod 4` branch. -/
theorem dvd_four_sub_sq_of_exists_zsqrtd_image_of_ne_one_mod_four
    (d a' b' : ℤ) (hd : Squarefree d) (hd4 : d % 4 ≠ 1)
    (hz : ∃ z : Zsqrtd d, Zsqrtd.toQsqrtdHom d z = Zsqrtd.halfInt (d := d) a' b') :
    4 ∣ (a' ^ 2 - d * b' ^ 2) :=
  (dvd_four_sub_sq_iff_exists_zsqrtd_image_of_ne_one_mod_four d a' b' hd hd4).2 hz

/-- Generic fact: the ring of integers is ring-isomorphic to any integral closure model. -/
theorem ringOfIntegers_equiv_of_integralClosure
    (K : Type*) [Field K] [NumberField K]
    (R : Type*) [CommRing R] [Algebra R K] [IsIntegralClosure R ℤ K] :
    Nonempty (𝓞 K ≃+* R) := by
  exact ⟨NumberField.RingOfIntegers.equiv (K := K) (R := R)⟩

end RingOfIntegers
end QuadNumberField
