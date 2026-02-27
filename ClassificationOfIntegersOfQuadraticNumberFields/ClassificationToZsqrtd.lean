import Mathlib
import ClassificationOfIntegersOfQuadraticNumberFields.HalfInt
import ClassificationOfIntegersOfQuadraticNumberFields.ModFourCriteria

namespace ClassificationOfIntegersOfQuadraticNumberFields

open scoped NumberField

section ClassificationToZsqrtd

namespace Qsqrtd

/-- The canonical embedding `ℤ√d → Q(√d)` into the rational quadratic algebra model. -/
def zsqrtdToQsqrtd (d : ℤ) : ℤ√d →+* Qsqrtd d where
  toFun := fun z => ⟨(z.re : ℚ), (z.im : ℚ)⟩
  map_one' := by
    ext <;> rfl
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

/-- Forward branch criterion (`d % 4 ≠ 1`): divisibility implies representability in `ℤ√d`. -/
theorem exists_zsqrtd_image_of_dvd_four_sub_sq_of_ne_one_mod_four
    (d a' b' : ℤ) (hd : Squarefree d) (hd4 : d % 4 ≠ 1)
    (hdiv : 4 ∣ (a' ^ 2 - d * b' ^ 2)) :
    ∃ z : ℤ√d, zsqrtdToQsqrtd d z = halfInt d a' b' :=
  (dvd_four_sub_sq_iff_exists_zsqrtd_image_of_ne_one_mod_four d a' b' hd hd4).1 hdiv

/-- Reverse branch criterion (`d % 4 ≠ 1`): representability in `ℤ√d` implies divisibility. -/
theorem dvd_four_sub_sq_of_exists_zsqrtd_image_of_ne_one_mod_four
    (d a' b' : ℤ) (hd : Squarefree d) (hd4 : d % 4 ≠ 1)
    (hz : ∃ z : ℤ√d, zsqrtdToQsqrtd d z = halfInt d a' b') :
    4 ∣ (a' ^ 2 - d * b' ^ 2) :=
  (dvd_four_sub_sq_iff_exists_zsqrtd_image_of_ne_one_mod_four d a' b' hd hd4).2 hz

/-- Generic fact: the ring of integers is ring-isomorphic to any integral closure model. -/
theorem ringOfIntegers_equiv_of_integralClosure
    (K : Type*) [Field K] [NumberField K]
    (R : Type*) [CommRing R] [Algebra R K] [IsIntegralClosure R ℤ K] :
    Nonempty (𝓞 K ≃+* R) := by
  exact ⟨NumberField.RingOfIntegers.equiv (K := K) (R := R)⟩

/-- The image type of `zsqrtdToQsqrtd`. -/
abbrev zsqrtdRange (d : ℤ) : Type := (zsqrtdToQsqrtd d).range

/-- Forward direction: if `d % 4 ≠ 1`, then `𝓞 (Q(√d))` is ring-isomorphic to `ℤ√d`. -/
lemma ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one
    (d : ℤ) [IsQuadraticParam d] [NumberField (Qsqrtd d)]
    (hd4 : d % 4 ≠ 1) :
    Nonempty (𝓞 (Qsqrtd d) ≃+* ℤ√d) := by
  sorry

/-- Reverse direction: if `𝓞 (Q(√d))` is ring-isomorphic to `ℤ√d`, then `d % 4 ≠ 1`. -/
lemma mod_four_ne_one_of_ringOfIntegers_equiv_zsqrtd
    (d : ℤ) [IsQuadraticParam d] [NumberField (Qsqrtd d)]
    (hiso : Nonempty (𝓞 (Qsqrtd d) ≃+* ℤ√d)) :
    d % 4 ≠ 1 := by
  -- Planned route:
  -- 1) Assume `d % 4 = 1`.
  -- 2) Show `(1 + √d) / 2` is integral in `Qsqrtd d`.
  -- 3) Show this element is not in the canonical `ℤ√d` image.
  -- 4) Contradict `hiso` by transferring integrally-closedness / integral-closure characterization.
  sorry

/-- Classification target (isomorphism form):
`𝓞 (Q(√d)) ≃+* ℤ√d` iff `d % 4 ≠ 1`.

This is the formal replacement of the informal equality
`𝓞 (Q(√d)) = ℤ√d`. -/
theorem ringOfIntegers_equiv_zsqrtd_iff_mod_four_ne_one
    (d : ℤ) [IsQuadraticParam d] [NumberField (Qsqrtd d)] :
    (d % 4 ≠ 1) ↔ Nonempty (𝓞 (Qsqrtd d) ≃+* ℤ√d) := by
  constructor
  · exact ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one d
  · exact mod_four_ne_one_of_ringOfIntegers_equiv_zsqrtd d



/- NOTE:
The `d % 4 = 1` branch should classify integral elements via `ℤ[(1+√d)/2]`.
We leave that branch for future work. -/

end Qsqrtd

end ClassificationToZsqrtd
end ClassificationOfIntegersOfQuadraticNumberFields
