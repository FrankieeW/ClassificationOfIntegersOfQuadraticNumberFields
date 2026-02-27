import Mathlib
import ClassificationOfIntegersOfQuadraticNumberFields.HalfInt
import ClassificationOfIntegersOfQuadraticNumberFields.ModFourCriteria

namespace ClassificationOfIntegersOfQuadraticNumberFields

section ClassificationToZsqrtd

namespace Qsqrtd

/-- The canonical embedding `ℤ√d → Q(√d)` into the rational quadratic algebra model. -/
def zsqrtdToQsqrtd (d : ℤ) : ℤ√d →+* Qsqrtd d where
  toFun := fun z => ⟨(z.re : ℚ), (z.im : ℚ)⟩
  map_one' := by ext <;> simp
  map_mul' := by
    intro z w
    ext <;> simp [mul_assoc, mul_comm, mul_left_comm]
  map_zero' := by ext <;> simp
  map_add' := by intro z w; ext <;> simp

/-- The canonical embedding `ℤ√d → Q(√d)` is injective. -/
theorem zsqrtdToQsqrtd_injective (d : ℤ) : Function.Injective (zsqrtdToQsqrtd d) := by
  intro z w hzw
  ext
  · simpa [zsqrtdToQsqrtd] using congrArg QuadraticAlgebra.re hzw
  · simpa [zsqrtdToQsqrtd] using congrArg QuadraticAlgebra.im hzw

/-- `ℤ√d` is ring-isomorphic to its image in `Q(√d)`. -/
noncomputable def zsqrtdEquivRangeQsqrtd (d : ℤ) : ℤ√d ≃+* (zsqrtdToQsqrtd d).range := by
  refine RingEquiv.ofBijective (zsqrtdToQsqrtd d).rangeRestrict ?_
  constructor
  · intro z w hzw
    exact zsqrtdToQsqrtd_injective d (Subtype.ext_iff.mp hzw)
  · intro x
    rcases x.property with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    exact Subtype.ext hz

/-- A half-integral element is in the image of `ℤ√d` iff both numerators are even. -/
theorem halfInt_mem_range_zsqrtdToQsqrtd_iff_even_even (d a' b' : ℤ) :
    (∃ z : ℤ√d, zsqrtdToQsqrtd d z = halfInt d a' b') ↔ (2 ∣ a' ∧ 2 ∣ b') := by
  constructor
  · rintro ⟨z, hz⟩
    have hm : (a' : ℚ) / 2 = z.re := by
      simpa [halfInt, zsqrtdToQsqrtd] using congrArg QuadraticAlgebra.re hz.symm
    have hn : (b' : ℚ) / 2 = z.im := by
      simpa [halfInt, zsqrtdToQsqrtd] using congrArg QuadraticAlgebra.im hz.symm
    have ha : 2 ∣ a' := by
      refine ⟨z.re, ?_⟩
      have hq : (a' : ℚ) = 2 * z.re := by nlinarith [hm]
      exact_mod_cast hq
    have hb : 2 ∣ b' := by
      refine ⟨z.im, ?_⟩
      have hq : (b' : ℚ) = 2 * z.im := by nlinarith [hn]
      exact_mod_cast hq
    exact ⟨ha, hb⟩
  · rintro ⟨ha, hb⟩
    rcases ha with ⟨m, hm⟩
    rcases hb with ⟨n, hn⟩
    refine ⟨⟨m, n⟩, ?_⟩
    ext <;> simp [halfInt, zsqrtdToQsqrtd, hm, hn]

/-- Classification (`d % 4 ≠ 1` branch): the mod-4 condition is exactly representability
as an element of mathlib's `ℤ√d` inside `Q(√d)`. -/
theorem dvd_four_sub_sq_iff_exists_zsqrtd_image_of_ne_one_mod_four
    (d a' b' : ℤ) (hd : Squarefree d) (hd4 : d % 4 ≠ 1) :
    4 ∣ (a' ^ 2 - d * b' ^ 2) ↔ ∃ z : ℤ√d, zsqrtdToQsqrtd d z = halfInt d a' b' := by
  rw [dvd_four_sub_sq_iff_even_even_of_ne_one_mod_four d a' b' hd hd4]
  rw [halfInt_mem_range_zsqrtdToQsqrtd_iff_even_even]

/- NOTE:
The `d % 4 = 1` branch should classify integral elements via `ℤ[(1+√d)/2]`.
We leave that branch for future work. -/

end Qsqrtd

end ClassificationToZsqrtd
end ClassificationOfIntegersOfQuadraticNumberFields
