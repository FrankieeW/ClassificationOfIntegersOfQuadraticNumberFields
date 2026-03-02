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

This file contains the final classification theorem for
`𝓞 (QuadNumberField d)`.

## Main Results

* `ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one`:
  if `d % 4 ≠ 1` then `𝓞 (Q(√d)) ≃+* ℤ√d`.
* `ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one`:
  if `d % 4 = 1` then `𝓞 (Q(√d)) ≃+* ℤ[(1+√d)/2]`.
* `ringOfIntegers_classification`:
  combines both branches into a single disjunction.

## Design

Integrality ingredients (`IsIntegralClosure` constructions,
half-integer normal form, etc.) live in `Integrality.lean`.
This file assembles the final `𝓞 ≃+* R` isomorphisms and the
top-level classification.
-/

open scoped NumberField

namespace QuadNumberField
namespace RingOfIntegers

/-- If `d % 4 ≠ 1`, then `𝓞 (Q(√d)) ≃+* ℤ√d`. -/
theorem ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one
    (d : ℤ) [QuadFieldParam d]
    [NumberField (QuadNumberField d)]
    (hd4 : d % 4 ≠ 1) :
    Nonempty (𝓞 (QuadNumberField d) ≃+* Zsqrtd d) := by
  letI : Algebra (Zsqrtd d) (QuadNumberField d) :=
    (Zsqrtd.toQsqrtdHom d).toAlgebra
  let hIC : IsIntegralClosure (Zsqrtd d) ℤ
      (QuadNumberField d) :=
    { algebraMap_injective := by
        simpa [RingHom.toAlgebra, QuadNumberField] using
          (Zsqrtd.toQsqrtdHom_injective d)
      isIntegral_iff := by
        intro x
        constructor
        · intro hx
          rcases exists_zsqrtd_of_isIntegral_of_ne_one_mod_four
            d hd4 (x := x) hx with ⟨z, hz⟩
          exact ⟨z, by simpa [RingHom.toAlgebra,
            QuadNumberField] using hz⟩
        · rintro ⟨z, rfl⟩
          simpa [RingHom.toAlgebra, QuadNumberField] using
            (isIntegral_toQsqrtd d z) }
  exact ⟨@NumberField.RingOfIntegers.equiv
    (QuadNumberField d)
    (inferInstance : Field (QuadNumberField d))
    (Zsqrtd d)
    (inferInstance : CommRing (Zsqrtd d))
    ((Zsqrtd.toQsqrtdHom d).toAlgebra)
    hIC⟩

/-- If `d % 4 = 1`, writing `d = 1 + 4k`,
then `𝓞 (Q(√d)) ≃+* ZOnePlusSqrtOverTwo k`. -/
theorem ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one
    (d : ℤ) [QuadFieldParam d]
    [NumberField (QuadNumberField d)]
    (hd4 : d % 4 = 1) :
    ∃ k : ℤ, d = 1 + 4 * k ∧
      Nonempty (𝓞 (QuadNumberField d) ≃+*
        ZOnePlusSqrtOverTwo k) := by
  rcases exists_k_of_mod_four_eq_one (d := d) hd4 with ⟨k, hk⟩
  refine ⟨k, hk, ?_⟩
  subst hk
  letI : Algebra (ZOnePlusSqrtOverTwo k)
      (QuadNumberField (1 + 4 * k)) :=
    (_root_.ZOnePlusSqrtOverTwo.toQsqrtdHom k).toAlgebra
  let hIC : IsIntegralClosure (ZOnePlusSqrtOverTwo k) ℤ
      (QuadNumberField (1 + 4 * k)) :=
    { algebraMap_injective := by
        simpa [RingHom.toAlgebra, QuadNumberField] using
          (_root_.ZOnePlusSqrtOverTwo.toQsqrtdHom_injective k)
      isIntegral_iff := by
        intro x
        constructor
        · intro hx
          rcases exists_zOnePlusSqrtOverTwo_of_isIntegral_of_one_mod_four
            k (x := x) hx with ⟨z, hz⟩
          exact ⟨z, by simpa [RingHom.toAlgebra,
            QuadNumberField] using hz⟩
        · rintro ⟨z, rfl⟩
          simpa [RingHom.toAlgebra, QuadNumberField] using
            (isIntegral_toQsqrtd_of_zOnePlusSqrtOverTwo k z) }
  exact ⟨@NumberField.RingOfIntegers.equiv
    (QuadNumberField (1 + 4 * k))
    (inferInstance : Field (QuadNumberField (1 + 4 * k)))
    (ZOnePlusSqrtOverTwo k)
    (inferInstance : CommRing (ZOnePlusSqrtOverTwo k))
    ((_root_.ZOnePlusSqrtOverTwo.toQsqrtdHom k).toAlgebra)
    hIC⟩

/-- **Classification of the ring of integers of `Q(√d)`.**

For squarefree `d`, exactly one of the following holds:
* If `d % 4 ≠ 1`, then `𝓞 (Q(√d)) ≃+* ℤ√d`.
* If `d % 4 = 1`, then writing `d = 1 + 4k`,
  `𝓞 (Q(√d)) ≃+* ℤ[(1+√d)/2]`. -/
theorem ringOfIntegers_classification
    (d : ℤ) [QuadFieldParam d]
    [NumberField (QuadNumberField d)] :
    (d % 4 ≠ 1 ∧
      Nonempty (𝓞 (QuadNumberField d) ≃+* Zsqrtd d)) ∨
    (∃ k : ℤ, d = 1 + 4 * k ∧
      Nonempty (𝓞 (QuadNumberField d) ≃+*
        ZOnePlusSqrtOverTwo k)) := by
  by_cases hd4 : d % 4 = 1
  · right
    exact ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one
      d hd4
  · left
    exact ⟨hd4,
      ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one d hd4⟩

end RingOfIntegers
end QuadNumberField
