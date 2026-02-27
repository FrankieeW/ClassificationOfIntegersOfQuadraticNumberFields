import Mathlib
import ClassificationOfIntegersOfQuadraticNumberFields.Base

/-!
# Non-isomorphism of quadratic fields with distinct parameters

This file proves that two quadratic fields `ℚ(√d₁)` and `ℚ(√d₂)` are not
isomorphic (as `ℚ`-algebras) whenever `d₁ ≠ d₂` and both are squarefree
nonzero integers.

The proof strategy is:
1. Suppose an isomorphism `e : ℚ(√d₁) ≃ₐ[ℚ] ℚ(√d₂)` exists.
2. The image `x = e(√d₁)` satisfies `x² = d₁` inside `ℚ(√d₂)`.
3. Expanding in the basis `{1, √d₂}`, the imaginary part equation forces
   `x.re * x.im = 0`, giving two cases.
4. In either case we derive that `d₁/d₂` is a square in `ℚ`.
5. A denominator argument using squarefreeness shows `d₂ ∣ d₁` and `d₁ ∣ d₂`,
   so `d₁` and `d₂` are associates in `ℤ`.
6. Associates in `ℤ` means `d₁ = d₂` or `d₁ = -d₂`; the former contradicts
   `d₁ ≠ d₂`, and the latter implies `-1` is a square in `ℚ`, a contradiction.
-/

namespace ClassificationOfIntegersOfQuadraticNumberFields
namespace Qsqrtd

/-- `-1` is not a square in `ℚ`. Any rational square `r * r` is nonneg, but `-1 < 0`. -/
lemma not_isSquare_neg_one_rat : ¬ IsSquare (- (1 : ℚ)) := by
  rintro ⟨r, hr⟩
  have hnonneg : 0 ≤ r ^ 2 := sq_nonneg r
  nlinarith [hr, hnonneg]

/-- If `m : ℕ` is squarefree as an integer and is a square in `ℤ`, then `m = 1`.
    A squarefree integer that is also a perfect square must be a unit. -/
lemma nat_eq_one_of_squarefree_intcast_of_isSquare (m : ℕ)
    (hsm : Squarefree (m : ℤ)) (hsq : IsSquare (m : ℤ)) : m = 1 := by
  rcases hsq with ⟨z, hz⟩
  -- Case split: is the square root `z` a unit (i.e. ±1)?
  by_cases huz : IsUnit z
  · -- If z is a unit, then m = z * z = (±1)² = 1.
    rcases Int.isUnit_iff.mp huz with hz1 | hz1
    · have hmz : (m : ℤ) = 1 := by simpa [hz1] using hz
      norm_num at hmz
      exact hmz
    · have hmz : (m : ℤ) = 1 := by simpa [hz1] using hz
      norm_num at hmz
      exact hmz
  · -- If z is not a unit, then z² being squarefree is impossible
    -- (squarefree means every factor appears at most once, but z appears twice).
    have hsqz2 : Squarefree (z ^ 2) := by simpa [hz, pow_two] using hsm
    have h01 : (2 : ℕ) = 0 ∨ (2 : ℕ) = 1 :=
      Squarefree.eq_zero_or_one_of_pow_of_not_isUnit (x := z) (n := 2) hsqz2 huz
    norm_num at h01

/-- If `d₂` is squarefree and nonzero, and `d₁ / d₂` is a square in `ℚ`, then `d₂ ∣ d₁`.

    The key idea: write `d₁/d₂` in lowest terms as `p/q`. The denominator `q` divides `d₂`,
    so `q` is also squarefree. But `d₁/d₂` being a square forces `q` to be a square as well.
    A squarefree square must be 1, meaning `d₂` divides `d₁`. -/
lemma int_dvd_of_ratio_square (d₁ d₂ : ℤ) (hd₂ : d₂ ≠ 0)
    (hsq_d₂ : Squarefree d₂) (hr : IsSquare ((d₁ : ℚ) / (d₂ : ℚ))) : d₂ ∣ d₁ := by
  -- The denominator of d₁/d₂ (in lowest terms) is a square.
  have hsq_den_nat : IsSquare (((d₁ : ℚ) / (d₂ : ℚ)).den) := (Rat.isSquare_iff.mp hr).2
  -- Lift the squareness to ℤ.
  have hsq_den_int : IsSquare ((((d₁ : ℚ) / (d₂ : ℚ)).den : ℤ)) := by
    rcases hsq_den_nat with ⟨n, hn⟩
    refine ⟨(n : ℤ), by exact_mod_cast hn⟩
  -- The denominator of d₁/d₂ divides d₂.
  have hden_dvd : ((((d₁ : ℚ) / (d₂ : ℚ)).den : ℤ)) ∣ d₂ := by
    simpa [← Rat.divInt_eq_div] using (Rat.den_dvd d₁ d₂)
  -- Since it divides the squarefree d₂, the denominator is itself squarefree.
  have hsqf_den_int : Squarefree ((((d₁ : ℚ) / (d₂ : ℚ)).den : ℤ)) :=
    Squarefree.squarefree_of_dvd hden_dvd hsq_d₂
  -- Squarefree + square ⟹ denominator = 1, so d₂ ∣ d₁.
  have hden1_nat : ((d₁ : ℚ) / (d₂ : ℚ)).den = 1 :=
    nat_eq_one_of_squarefree_intcast_of_isSquare _ hsqf_den_int hsq_den_int
  exact (Rat.den_div_intCast_eq_one_iff d₁ d₂ hd₂).1 hden1_nat

/-- **Main theorem**: Distinct squarefree parameters define non-isomorphic quadratic fields.

    If `d₁ ≠ d₂` are both squarefree nonzero integers, then there is no `ℚ`-algebra
    isomorphism `ℚ(√d₁) ≃ₐ[ℚ] ℚ(√d₂)`. -/
theorem quadratic_fields_not_iso
    (d1 d2 : ℤ) [IsQuadraticParam d1] [IsQuadraticParam d2]
    (hneq : d1 ≠ d2) :
    ¬ Nonempty (Qsqrtd d1 ≃ₐ[ℚ] Qsqrtd d2) := by
  rintro ⟨e⟩
  -- Let x = e(√d₁) ∈ ℚ(√d₂). Write x = a + b√d₂ for some a, b ∈ ℚ.
  let x : Qsqrtd d2 := e ⟨0, 1⟩
  -- Since e is a ring homomorphism and (√d₁)² = d₁, we get x² = d₁ in ℚ(√d₂).
  have hx : x * x = (d1 : Qsqrtd d2) := by
    change e ⟨0, 1⟩ * e ⟨0, 1⟩ = (d1 : Qsqrtd d2)
    calc
      e ⟨0, 1⟩ * e ⟨0, 1⟩ = e ((⟨0, 1⟩ : Qsqrtd d1) * ⟨0, 1⟩) := by
        symm
        exact e.map_mul _ _
      _ = e (d1 : Qsqrtd d1) := by
        congr 1
        ext <;> simp [Qsqrtd]
      _ = (d1 : Qsqrtd d2) := by simp
  -- Expanding x² = (a + b√d₂)² = (a² + b²d₂) + 2ab√d₂, the imaginary part gives 2ab = 0.
  have him0 : (x * x).im = 0 := by
    have him := congrArg QuadraticAlgebra.im hx
    simpa [Qsqrtd] using him
  have hsum : x.re * x.im + x.im * x.re = 0 := by
    simpa [Qsqrtd, mul_assoc, mul_comm, mul_left_comm] using him0
  -- So either a = 0 or b = 0.
  have hprod : x.re * x.im = 0 := by nlinarith [hsum]
  -- In either case, d₁/d₂ is a perfect square in ℚ.
  have hratio : IsSquare ((d1 : ℚ) / (d2 : ℚ)) := by
    rcases mul_eq_zero.mp hprod with hre | him
    · -- Case a = 0: then x = b√d₂, so x² = b²d₂ = d₁, giving d₁/d₂ = b².
      refine ⟨x.im, ?_⟩
      have hre0 : (x * x).re = d1 := by
        have hre' := congrArg QuadraticAlgebra.re hx
        simpa [Qsqrtd] using hre'
      have hmain : (d2 : ℚ) * (x.im ^ 2) = d1 := by
        simpa [Qsqrtd, hre, pow_two, mul_assoc, mul_comm, mul_left_comm] using hre0
      have hd2Q : (d2 : ℚ) ≠ 0 := by
        exact_mod_cast (IsQuadraticParam.ne_zero (d := d2))
      calc
        (d1 : ℚ) / (d2 : ℚ) = (((d2 : ℚ) * (x.im ^ 2)) / (d2 : ℚ)) := by simp [hmain]
        _ = x.im ^ 2 := by field_simp [hd2Q]
        _ = x.im * x.im := by ring
    · -- Case b = 0: then x = a ∈ ℚ, so x² = a² = d₁, contradicting d₁ nonsquare.
      exfalso
      have hre0 : (x * x).re = d1 := by
        have hre' := congrArg QuadraticAlgebra.re hx
        simpa [Qsqrtd] using hre'
      have hmain : x.re ^ 2 = d1 := by
        simpa [Qsqrtd, him, pow_two, mul_assoc, mul_comm, mul_left_comm] using hre0
      exact (IsNonsquareRat.nonsquare (d := d1) x.re) hmain
  -- Now use the squarefreeness argument to derive d₂ ∣ d₁ and d₁ ∣ d₂.
  have hd1 : d1 ≠ 0 := IsQuadraticParam.ne_zero (d := d1)
  have hd2 : d2 ≠ 0 := IsQuadraticParam.ne_zero (d := d2)
  -- d₁/d₂ is a square ⟹ d₂/d₁ is also a square (take inverse of the witness).
  have hratio' : IsSquare ((d2 : ℚ) / (d1 : ℚ)) := by
    rcases hratio with ⟨r, hr⟩
    refine ⟨r⁻¹, ?_⟩
    have hd1Q : (d1 : ℚ) ≠ 0 := by exact_mod_cast hd1
    have hd2Q : (d2 : ℚ) ≠ 0 := by exact_mod_cast hd2
    have h1 : (r⁻¹ * r⁻¹) = (((d1 : ℚ) / (d2 : ℚ)))⁻¹ := by
      simp [hr]
    calc
      ((d2 : ℚ) / (d1 : ℚ)) = (((d1 : ℚ) / (d2 : ℚ)))⁻¹ := by
        field_simp [hd1Q, hd2Q]
      _ = r⁻¹ * r⁻¹ := h1.symm
  -- By the denominator lemma: d₂ ∣ d₁ and d₁ ∣ d₂.
  have hd21 : d2 ∣ d1 :=
    int_dvd_of_ratio_square d1 d2 hd2 (IsQuadraticParam.squarefree (d := d2)) hratio
  have hd12 : d1 ∣ d2 :=
    int_dvd_of_ratio_square d2 d1 hd1 (IsQuadraticParam.squarefree (d := d1)) hratio'
  -- Mutual divisibility ⟹ d₁ and d₂ are associates, i.e. d₁ = ±d₂.
  have hassoc : Associated d1 d2 := associated_of_dvd_dvd hd12 hd21
  rcases (Int.associated_iff.mp hassoc) with hEq | hNeg
  · -- d₁ = d₂ contradicts our hypothesis d₁ ≠ d₂.
    exact hneq hEq
  · -- d₁ = -d₂ means d₁/d₂ = -1, so -1 is a square in ℚ — contradiction.
    have hd2Q : (d2 : ℚ) ≠ 0 := by exact_mod_cast hd2
    have hratio_neg1 : ((d1 : ℚ) / (d2 : ℚ)) = (-1 : ℚ) := by
      rw [hNeg]
      simp
      field_simp [hd2Q]
    have hsq_neg1 : IsSquare (- (1 : ℚ)) := by rwa [hratio_neg1] at hratio
    exact not_isSquare_neg_one_rat hsq_neg1

end Qsqrtd
end ClassificationOfIntegersOfQuadraticNumberFields
