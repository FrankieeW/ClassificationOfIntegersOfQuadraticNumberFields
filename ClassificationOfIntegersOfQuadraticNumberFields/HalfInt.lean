import Mathlib
import ClassificationOfIntegersOfQuadraticNumberFields.MinimalPolynomial

namespace ClassificationOfIntegersOfQuadraticNumberFields
namespace Qsqrtd

/-- The element `(a' + b'√d)/2` in `Q(√d)`. -/
def halfInt (d : ℤ) (a' b' : ℤ) : Qsqrtd d :=
  ⟨a' / 2, b' / 2⟩

/-- Trace of `halfInt` is `a'`. -/
theorem trace_halfInt (d a' b' : ℤ) : trace (halfInt d a' b') = a' := by
  have : (halfInt d a' b').re = a' / 2 := rfl
  rw [trace_eq_two_re, this]
  ring

/-- Norm of `halfInt` is `(a'² - d*b'²)/4`. -/
theorem norm_halfInt (d a' b' : ℤ) :
    norm' (halfInt d a' b') = (a' ^ 2 - (d : ℚ) * b' ^ 2) / 4 := by
  have re_eq : (halfInt d a' b').re = a' / 2 := rfl
  have im_eq : (halfInt d a' b').im = b' / 2 := rfl
  rw [norm_eq_sqr_minus_d_sqr, re_eq, im_eq]
  ring

end Qsqrtd
end ClassificationOfIntegersOfQuadraticNumberFields
