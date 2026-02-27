import Mathlib
import ClassificationOfIntegersOfQuadraticNumberFields.Base

namespace ClassificationOfIntegersOfQuadraticNumberFields
namespace Qsqrtd

/-- The trace of an element in `Q(√d)` is `2 * re`. -/
theorem trace_eq_two_re {d : ℤ} (x : Qsqrtd d) : trace x = 2 * x.re := by
  have star_re : (star x).re = x.re := by
    simp [star, star]
  simp [trace, star_re]
  ring

/-- The norm of an element in `Q(√d)` is `re² - d * im²`. -/
theorem norm_eq_sqr_minus_d_sqr {d : ℤ} (x : Qsqrtd d) :
    norm' x = x.re ^ 2 - (d : ℚ) * x.im ^ 2 := by
  simp [norm', QuadraticAlgebra.norm]
  ring

/-- Quadratic identity: `x` is a root of `X² - trace(x) X + norm(x)`. -/
theorem aeval_eq_zero_of_quadratic (d : ℤ) (x : Qsqrtd d) :
    x * x - (algebraMap ℚ (Qsqrtd d) (x.trace)) • x + (algebraMap ℚ (Qsqrtd d) (norm' x)) = 0 := by
  ext <;> simp [trace, norm', QuadraticAlgebra.norm, star, smul_eq_mul] <;> ring

end Qsqrtd
end ClassificationOfIntegersOfQuadraticNumberFields
