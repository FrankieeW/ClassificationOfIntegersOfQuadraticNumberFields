import Mathlib
import ClassificationOfIntegersOfQuadraticNumberFields.Base

open ClassificationOfIntegersOfQuadraticNumberFields
open scoped NumberField
open Polynomial

namespace Qsqrtd

private lemma halfInt_one_one_isIntegral (d : ℤ) [IsQuadraticParam d]
    [NumberField (Qsqrtd d)] (hd4 : d % 4 = 1) :
    IsIntegral ℤ (⟨(1:ℚ)/2, (1:ℚ)/2⟩ : Qsqrtd d) := by
  set c : ℤ := (1 - d) / 4
  set ω : Qsqrtd d := ⟨(1:ℚ)/2, (1:ℚ)/2⟩
  refine ⟨X ^ 2 + (C (-1 : ℤ) * X + C c), ?_, ?_⟩
  · refine (monic_X_pow (R := ℤ) 2).add_of_left ?_
    calc (C (-1 : ℤ) * X + C c).degree
        ≤ max (C (-1 : ℤ) * X).degree (C c).degree := degree_add_le _ _
      _ ≤ max 1 0 := max_le_max (degree_C_mul_X_le _) degree_C_le
      _ < 2 := by norm_num
      _ = (X ^ 2 : ℤ[X]).degree := by simp
  · simp only [eval₂_add, eval₂_mul, eval₂_X, eval₂_C, sq]
    have hc4 : 4 * ((1 - d) / 4) = 1 - d := by omega
    have hc_cast : (4 : ℚ) * ((c : ℤ) : ℚ) = 1 - (d : ℚ) := by exact_mod_cast hc4
    ext
    · simp [ω]; linarith
    · simp [ω, c]; ring

-- Now the full proof
lemma mod_four_ne_one_of_ringOfIntegers_equiv_zsqrtd'
    (d : ℤ) [IsQuadraticParam d] [NumberField (Qsqrtd d)]
    (hiso : Nonempty (𝓞 (Qsqrtd d) ≃+* ℤ√d)) :
    d % 4 ≠ 1 := by
  intro hd4
  rcases hiso with ⟨φ⟩
  set ω : Qsqrtd d := ⟨(1:ℚ)/2, (1:ℚ)/2⟩
  have hω_int : IsIntegral ℤ ω := halfInt_one_one_isIntegral d hd4
  set ω' : 𝓞 (Qsqrtd d) := ⟨ω, hω_int⟩
  set z := φ ω'
  -- ω'² - ω' = (d-1)/4 · 1 in 𝓞(Q(√d))
  have hω_eq : ω' * ω' - ω' = ((d - 1) / 4 : ℤ) • (1 : 𝓞 (Qsqrtd d)) := by
    ext
    simp only [ω', ω, Subtype.val_eq_coe]
    simp [NumberField.RingOfIntegers, zsmul_eq_mul]
    constructor
    · -- re
      sorry
    · -- im
      sorry
  sorry

end Qsqrtd