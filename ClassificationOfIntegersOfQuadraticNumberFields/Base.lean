import Mathlib

namespace ClassificationOfIntegersOfQuadraticNumberFields

/-!
## §2.1 Quadratic integer rings — canonical parameters

A quadratic field is `ℚ(√d) = {a + b√d | a, b ∈ ℚ}` for some `d ∈ ℚ×`.
We restrict `d` to **squarefree integers ≠ 0, 1** for three reasons:

1. **`d ≠ 0`**: otherwise `√d = 0` and `ℚ(√0) = ℚ`, not a quadratic extension.
2. **`d ≠ 1`**: otherwise `√1 = 1 ∈ ℚ` and `ℚ(√1) = ℚ`, again trivial.
3. **`Squarefree d`**: for any `a ∈ ℚ×` we have `ℚ(√d) = ℚ(√(a²d))`, so every
   quadratic field has a unique squarefree integer representative.

Together these conditions make `IsQuadraticParam d` exactly the standard
canonical form for quadratic field parameters.
-/

/-- Parameters for quadratic fields `ℚ(√d)`: nonzero, nontrivial, and squarefree. -/
class IsQuadraticParam (d : ℤ) : Prop where
  /-- `d ≠ 0` and `d ≠ 1` ensure `ℚ(√d)` is not just `ℚ`. -/
  ne_zero : d ≠ 0
  ne_one : d ≠ 1
  /-- `Squarefree d` gives a canonical representative for the field. -/
  squarefree : Squarefree d

/-- The ambient type `Q(√d)`. -/
abbrev Qsqrtd (d : ℤ) : Type := QuadraticAlgebra ℚ (d : ℚ) 0

open QuadraticAlgebra
namespace Qsqrtd

/-- `ℚ(√d) ≃ₐ[ℚ] ℚ(√(a²d))` via `⟨r, s⟩ ↦ ⟨r, s·a⁻¹⟩`. -/
def rescale (d : ℚ) (a : ℚ) (ha : a ≠ 0) :
    QuadraticAlgebra ℚ d 0 ≃ₐ[ℚ] QuadraticAlgebra ℚ (a ^ 2 * d) 0 := by
  have h1d : (1 : QuadraticAlgebra ℚ d 0) = ⟨1, 0⟩ := by ext <;> rfl
  have h1a : (1 : QuadraticAlgebra ℚ (a ^ 2 * d) 0) = ⟨1, 0⟩ := by
    ext <;> rfl
  exact AlgEquiv.ofLinearEquiv
    { toFun := fun x => ⟨x.re, x.im * a⁻¹⟩
      invFun := fun y => ⟨y.re, y.im * a⟩
      map_add' := by intro x y; ext <;> simp [add_mul]
      map_smul' := by intro c x; ext <;> simp [mul_assoc]
      left_inv := by
        intro x; ext <;> simp [mul_assoc, inv_mul_cancel₀ ha]
      right_inv := by
        intro y; ext <;> simp [mul_assoc, mul_inv_cancel₀ ha] }
    (by simp [h1d, h1a])
    (by intro x y; ext <;> simp <;> field_simp)

/-- Trace on `Qsqrtd d` with dot notation `x.trace`. -/
abbrev trace {d : ℤ} (x : Qsqrtd d) : ℚ := x.re + (star x).re

/-- Norm on `Qsqrtd d`. -/
abbrev norm' {d : ℤ} (x : Qsqrtd d) : ℚ := QuadraticAlgebra.norm x

/-- Embedding of `ℚ` into `Qsqrtd d`. -/
abbrev embed (r : ℚ) : Qsqrtd d := algebraMap ℚ (Qsqrtd d) r

/-- Rational nonsquare condition for integer parameter `d`. -/
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
    exact (IsNonsquareRat.nonsquare (d := d) r) (by simp [hr])
  ⟩
  infer_instance

end Qsqrtd

end ClassificationOfIntegersOfQuadraticNumberFields
