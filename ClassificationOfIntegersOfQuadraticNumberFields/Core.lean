import Mathlib

namespace ClassificationOfIntegersOfQuadraticNumberFields

/-- Parameters for quadratic fields `ℚ(√d)`: nonzero, nontrivial, and squarefree. -/
class IsQuadraticParam (d : ℤ) : Prop where
  ne_zero : d ≠ 0
  ne_one : d ≠ 1
  squarefree : Squarefree d

/-- The ambient type `Q(√d)`. -/
abbrev Qsqrtd (d : ℤ) : Type := QuadraticAlgebra ℚ (d : ℚ) 0

namespace Qsqrtd

/-- Norm on `Qsqrtd d` with dot notation `x.norm`. -/
abbrev norm {d : ℤ} (x : Qsqrtd d) : ℚ := QuadraticAlgebra.norm x

/-- Trace on `Qsqrtd d` with dot notation `x.trace`. -/
abbrev trace {d : ℤ} (x : Qsqrtd d) : ℚ := x.re + (star x).re

class IsNonsquareRat (d : ℤ) : Prop where
  nonsquare : ∀ r : ℚ, r ^ 2 ≠ (d : ℚ)

/-- A squarefree nontrivial integer parameter is not a square in `ℤ`. -/
lemma not_isSquare_int (d : ℤ) [IsQuadraticParam d] : ¬ IsSquare d := by
  intro hdSq
  rcases hdSq with ⟨z, hz⟩
  by_cases huz : IsUnit z
  · rcases Int.isUnit_iff.mp huz with hz1 | hz1
    · have : d = 1 := by simpa [hz1] using hz
      exact (IsQuadraticParam.ne_one (d := d)) this
    · have : d = 1 := by simpa [hz1] using hz
      exact (IsQuadraticParam.ne_one (d := d)) this
  · have hsqz2 : Squarefree (z ^ 2) := by
      simpa [hz, pow_two] using (IsQuadraticParam.squarefree (d := d))
    have h01 : (2 : ℕ) = 0 ∨ (2 : ℕ) = 1 :=
      Squarefree.eq_zero_or_one_of_pow_of_not_isUnit (x := z) (n := 2) hsqz2 huz
    norm_num at h01

instance (d : ℤ) [IsQuadraticParam d] : IsNonsquareRat d := by
  refine ⟨?_⟩
  intro r hr
  have hsqQ : IsSquare ((d : ℤ) : ℚ) := ⟨r, by simpa [pow_two] using hr.symm⟩
  have hsqZ : IsSquare d := (Rat.isSquare_intCast_iff).1 hsqQ
  exact (not_isSquare_int d) hsqZ

instance {d : ℤ} [IsNonsquareRat d] : Field (Qsqrtd d) := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r) := ⟨by
    intro r hr
    exact (IsNonsquareRat.nonsquare (d := d) r) (by simpa [zero_mul, add_zero] using hr)
  ⟩
  infer_instance

/-- Exercise 2.4 (first part): `Q(√d)` is not linearly equivalent to `ℚ` over `ℚ`. -/
theorem qsqrtd_not_linearEquiv_rat (d : ℤ) [IsQuadraticParam d] :
    ¬ Nonempty (Qsqrtd d ≃ₗ[ℚ] ℚ) := by
  rintro ⟨e⟩
  have hfin : Module.finrank ℚ (Qsqrtd d) = Module.finrank ℚ ℚ :=
    LinearEquiv.finrank_eq e
  have hfin2 : Module.finrank ℚ (Qsqrtd d) = 2 := by
    simpa [Qsqrtd] using QuadraticAlgebra.finrank_eq_two (R := ℚ) (a := (d : ℚ)) (b := 0)
  have hfin1 : Module.finrank ℚ ℚ = 1 := Module.finrank_self ℚ
  have : (2 : ℕ) = 1 := by
    calc
      (2 : ℕ) = Module.finrank ℚ (Qsqrtd d) := by simp [hfin2]
      _ = Module.finrank ℚ ℚ := hfin
      _ = 1 := hfin1
  norm_num at this

end Qsqrtd

end ClassificationOfIntegersOfQuadraticNumberFields
