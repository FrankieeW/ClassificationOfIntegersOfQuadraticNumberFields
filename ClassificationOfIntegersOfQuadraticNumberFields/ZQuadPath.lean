import Mathlib
import ClassificationOfIntegersOfQuadraticNumberFields.HalfInt
import ClassificationOfIntegersOfQuadraticNumberFields.ModFourCriteria
import ClassificationOfIntegersOfQuadraticNumberFields.NonIso

namespace ClassificationOfIntegersOfQuadraticNumberFields

open QuadraticAlgebra
open scoped NumberField

/-- Integer quadratic algebra model used as an intermediate target. -/
abbrev ZQuad (d : ℤ) : Type := QuadraticAlgebra ℤ d 0

namespace ZQuad

/-- `ZQuad d → ℤ√d` by matching coordinates. -/
def toZsqrtd (d : ℤ) : ZQuad d →+* ℤ√d where
  toFun := fun x => ⟨x.re, x.im⟩
  map_one' := by
    ext <;> rfl
  map_mul' := by
    intro x y
    ext <;> simp
  map_zero' := by
    ext <;> rfl
  map_add' := by
    intro x y
    ext <;> rfl

/-- `ℤ√d → ZQuad d` by matching coordinates. -/
def ofZsqrtd (d : ℤ) : ℤ√d →+* ZQuad d where
  toFun := fun z => ⟨z.re, z.im⟩
  map_one' := by
    ext <;> rfl
  map_mul' := by
    intro x y
    ext <;> simp
  map_zero' := by
    ext <;> rfl
  map_add' := by
    intro x y
    ext <;> rfl

@[simp] theorem toZsqrtd_ofZsqrtd (d : ℤ) (z : ℤ√d) :
    toZsqrtd d (ofZsqrtd d z) = z := by
  ext <;> rfl

@[simp] theorem ofZsqrtd_toZsqrtd (d : ℤ) (x : ZQuad d) :
    ofZsqrtd d (toZsqrtd d x) = x := by
  ext <;> rfl

/-- Structural ring isomorphism between `ZQuad d` and mathlib's `ℤ√d`. -/
def equivZsqrtd (d : ℤ) : ZQuad d ≃+* ℤ√d where
  toFun := toZsqrtd d
  invFun := ofZsqrtd d
  left_inv := ofZsqrtd_toZsqrtd d
  right_inv := toZsqrtd_ofZsqrtd d
  map_mul' := by
    intro x y
    ext <;> simp [mul_comm, mul_left_comm]
  map_add' := by
    intro x y
    rfl

/-- Coordinate-wise cast embedding `ZQuad d → Q(√d)`. -/
def toQsqrtd (d : ℤ) : ZQuad d →+* Qsqrtd d where
  toFun := fun x => ⟨(x.re : ℚ), (x.im : ℚ)⟩
  map_one' := by
    ext <;> norm_num
  map_mul' := by
    intro x y
    ext <;> simp [mul_assoc, mul_comm, mul_left_comm]
  map_zero' := by
    ext <;> norm_num
  map_add' := by
    intro x y
    ext <;> simp

/-- The canonical map `ZQuad d → Q(√d)` is injective. -/
theorem toQsqrtd_injective (d : ℤ) : Function.Injective (toQsqrtd d) := by
  intro x y hxy
  ext
  · have hre : ((x.re : ℚ) : ℚ) = (y.re : ℚ) := by
      simpa [toQsqrtd] using congrArg QuadraticAlgebra.re hxy
    exact_mod_cast hre
  · have him : ((x.im : ℚ) : ℚ) = (y.im : ℚ) := by
      simpa [toQsqrtd] using congrArg QuadraticAlgebra.im hxy
    exact_mod_cast him

/-- Every element in the `ZQuad d` image is integral over `ℤ`. -/
lemma isIntegral_toQsqrtd (d : ℤ) (z : ZQuad d) : IsIntegral ℤ (toQsqrtd d z) := by
  have hz : IsIntegral ℤ z := Algebra.IsIntegral.isIntegral z
  exact map_isIntegral_int (toQsqrtd d) hz

/-- `halfInt` is in the image of `ZQuad d` iff both numerators are even. -/
theorem halfInt_mem_range_toQsqrtd_iff_even_even (d a' b' : ℤ) :
    (∃ z : ZQuad d, toQsqrtd d z = Qsqrtd.halfInt d a' b') ↔ (2 ∣ a' ∧ 2 ∣ b') := by
  constructor
  · rintro ⟨z, hz⟩
    have hm : (a' : ℚ) / 2 = z.re := by
      simpa [toQsqrtd, Qsqrtd.halfInt] using congrArg QuadraticAlgebra.re hz.symm
    have hn : (b' : ℚ) / 2 = z.im := by
      simpa [toQsqrtd, Qsqrtd.halfInt] using congrArg QuadraticAlgebra.im hz.symm
    refine ⟨?_, ?_⟩
    · refine ⟨z.re, ?_⟩
      have hq : (a' : ℚ) = 2 * z.re := by nlinarith [hm]
      exact_mod_cast hq
    · refine ⟨z.im, ?_⟩
      have hq : (b' : ℚ) = 2 * z.im := by nlinarith [hn]
      exact_mod_cast hq
  · rintro ⟨ha, hb⟩
    rcases ha with ⟨m, hm⟩
    rcases hb with ⟨n, hn⟩
    refine ⟨⟨m, n⟩, ?_⟩
    ext <;> simp [toQsqrtd, Qsqrtd.halfInt, hm, hn]

/-- `d % 4 ≠ 1` branch through `ZQuad d` image. -/
theorem dvd_four_sub_sq_iff_exists_zquad_image_of_ne_one_mod_four
    (d a' b' : ℤ) (hd : Squarefree d) (hd4 : d % 4 ≠ 1) :
    4 ∣ (a' ^ 2 - d * b' ^ 2) ↔ ∃ z : ZQuad d, toQsqrtd d z = Qsqrtd.halfInt d a' b' := by
  rw [dvd_four_sub_sq_iff_even_even_of_ne_one_mod_four d a' b' hd hd4]
  rw [halfInt_mem_range_toQsqrtd_iff_even_even]

/-- Forward branch criterion (`d % 4 ≠ 1`): divisibility implies representability in `ZQuad d`. -/
theorem exists_zquad_image_of_dvd_four_sub_sq_of_ne_one_mod_four
    (d a' b' : ℤ) (hd : Squarefree d) (hd4 : d % 4 ≠ 1)
    (hdiv : 4 ∣ (a' ^ 2 - d * b' ^ 2)) :
    ∃ z : ZQuad d, toQsqrtd d z = Qsqrtd.halfInt d a' b' :=
  (dvd_four_sub_sq_iff_exists_zquad_image_of_ne_one_mod_four d a' b' hd hd4).1 hdiv

/-- Reverse branch criterion (`d % 4 ≠ 1`): representability in `ZQuad d` implies divisibility. -/
theorem dvd_four_sub_sq_of_exists_zquad_image_of_ne_one_mod_four
    (d a' b' : ℤ) (hd : Squarefree d) (hd4 : d % 4 ≠ 1)
    (hz : ∃ z : ZQuad d, toQsqrtd d z = Qsqrtd.halfInt d a' b') :
    4 ∣ (a' ^ 2 - d * b' ^ 2) :=
  (dvd_four_sub_sq_iff_exists_zquad_image_of_ne_one_mod_four d a' b' hd hd4).2 hz

/-- Bridge: an isomorphism to `ZQuad d` yields an isomorphism to `ℤ√d`. -/
theorem ringOfIntegers_equiv_zsqrtd_of_ringOfIntegers_equiv_zquad
    (d : ℤ) [Field (Qsqrtd d)] [NumberField (Qsqrtd d)]
    (h : Nonempty (𝓞 (Qsqrtd d) ≃+* ZQuad d)) :
    Nonempty (𝓞 (Qsqrtd d) ≃+* ℤ√d) := by
  rcases h with ⟨e⟩
  exact ⟨e.trans (equivZsqrtd d)⟩

/-- Integrality classification in the `d % 4 ≠ 1` branch: integral elements of `Q(√d)`
lie in the image of `ZQuad d`. -/
lemma exists_zquad_of_isIntegral_of_ne_one_mod_four
    (d : ℤ) [IsQuadraticParam d] (hd4 : d % 4 ≠ 1)
    {x : Qsqrtd d} (hx : IsIntegral ℤ x) :
    ∃ z : ZQuad d, toQsqrtd d z = x := by
  have hd : Squarefree d := IsQuadraticParam.squarefree (d := d)
  have hd0 : d ≠ 0 := IsQuadraticParam.ne_zero (d := d)
  have hd0Q : (d : ℚ) ≠ 0 := by exact_mod_cast hd0
  let cHom : ℚ →+* Qsqrtd d :=
    { toFun := QuadraticAlgebra.C (a := (d : ℚ)) (b := (0 : ℚ))
      map_one' := by
        simp [QuadraticAlgebra.C_one]
      map_mul' := by
        intro r s
        simp [QuadraticAlgebra.C_mul]
      map_zero' := by
        simp [QuadraticAlgebra.C_zero]
      map_add' := by
        intro r s
        simp [QuadraticAlgebra.C_add] }
  have hc_inj : Function.Injective cHom := by
    intro r s hrs
    exact (QuadraticAlgebra.C_inj (R := ℚ) (a := (d : ℚ)) (b := (0 : ℚ))).1 hrs

  have hstar : IsIntegral ℤ (star x) := map_isIntegral_int (starRingEnd (Qsqrtd d)) hx

  have htraceAlg :
      IsIntegral ℤ (QuadraticAlgebra.C (a := (d : ℚ)) (b := (0 : ℚ)) (Qsqrtd.trace x)) := by
    have hsum : IsIntegral ℤ (x + star x) := hx.add hstar
    have hsum_eq :
        x + star x = QuadraticAlgebra.C (a := (d : ℚ)) (b := (0 : ℚ)) (Qsqrtd.trace x) := by
      ext
      · simp [Qsqrtd.trace, star, QuadraticAlgebra.C]
      · simp [star, QuadraticAlgebra.C]
    simpa [hsum_eq] using hsum
  have htraceRat : IsIntegral ℤ (Qsqrtd.trace x) :=
    (isIntegral_algHom_iff cHom.toIntAlgHom hc_inj).1 htraceAlg
  obtain ⟨a', ha'⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).1 htraceRat
  have ha'trace : (a' : ℚ) = Qsqrtd.trace x := by simpa using ha'

  have hnormAlg : IsIntegral ℤ (algebraMap ℚ (Qsqrtd d) (Qsqrtd.norm' x)) := by
    have hmul : algebraMap ℚ (Qsqrtd d) (Qsqrtd.norm' x) = x * star x := by
      simpa [Qsqrtd.norm', mul_comm] using
        (QuadraticAlgebra.algebraMap_norm_eq_mul_star (a := (d : ℚ)) (b := (0 : ℚ)) x)
    have hprod : IsIntegral ℤ (x * star x) := hx.mul hstar
    simpa [hmul] using hprod
  have hnormRat : IsIntegral ℤ (Qsqrtd.norm' x) :=
    (isIntegral_algHom_iff (algebraMap ℚ (Qsqrtd d)).toIntAlgHom
      (algebraMap ℚ (Qsqrtd d)).injective).1 hnormAlg
  obtain ⟨n', hn'⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).1 hnormRat
  have hn'norm : (n' : ℚ) = Qsqrtd.norm' x := by simpa using hn'

  let q : ℚ := 2 * x.im
  let m : ℤ := a' ^ 2 - 4 * n'

  have hre : x.re = (a' : ℚ) / 2 := by
    have htr : 2 * x.re = (a' : ℚ) := by
      calc
        2 * x.re = Qsqrtd.trace x := (Qsqrtd.trace_eq_two_re x).symm
        _ = (a' : ℚ) := ha'trace.symm
    nlinarith

  have hqmul : (d : ℚ) * q ^ 2 = (m : ℚ) := by
    have hnorm' :
        (n' : ℚ) = ((a' : ℚ) / 2) ^ 2 - (d : ℚ) * x.im ^ 2 := by
      calc
        (n' : ℚ) = Qsqrtd.norm' x := hn'norm
        _ = x.re ^ 2 - (d : ℚ) * x.im ^ 2 := Qsqrtd.norm_eq_sqr_minus_d_sqr x
        _ = ((a' : ℚ) / 2) ^ 2 - (d : ℚ) * x.im ^ 2 := by simp [hre]
    have haux : (a' : ℚ) ^ 2 - 4 * (n' : ℚ) = 4 * (d : ℚ) * x.im ^ 2 := by
      nlinarith [hnorm']
    have hqmul' : (d : ℚ) * (2 * x.im) ^ 2 = (a' : ℚ) ^ 2 - 4 * (n' : ℚ) := by
      calc
        (d : ℚ) * (2 * x.im) ^ 2 = 4 * (d : ℚ) * x.im ^ 2 := by ring
        _ = (a' : ℚ) ^ 2 - 4 * (n' : ℚ) := by linarith [haux]
    have hmcast : (m : ℚ) = (a' : ℚ) ^ 2 - 4 * (n' : ℚ) := by
      dsimp [m]
      norm_cast
    dsimp [q]
    calc
      (d : ℚ) * (2 * x.im) ^ 2 = 4 * (d : ℚ) * x.im ^ 2 := by ring
      _ = (a' : ℚ) ^ 2 - 4 * (n' : ℚ) := by linarith [haux]
      _ = (m : ℚ) := hmcast.symm

  have hqratio : q ^ 2 = (m : ℚ) / (d : ℚ) := by
    calc
      q ^ 2 = ((d : ℚ) * q ^ 2) / (d : ℚ) := by field_simp [hd0Q]
      _ = (m : ℚ) / (d : ℚ) := by simp [hqmul]

  have hsqratio : IsSquare ((m : ℚ) / (d : ℚ)) := ⟨q, by simpa [pow_two] using hqratio.symm⟩
  have hdm : d ∣ m := Qsqrtd.int_dvd_of_ratio_square m d hd0 hd hsqratio
  rcases hdm with ⟨k, hk⟩
  have hq2 : q ^ 2 = (k : ℚ) := by
    have hmk : (m : ℚ) = (d : ℚ) * k := by
      exact_mod_cast hk
    calc
      q ^ 2 = (m : ℚ) / (d : ℚ) := hqratio
      _ = (((d : ℚ) * k) / (d : ℚ)) := by simp [hmk]
      _ = (k : ℚ) := by field_simp [hd0Q]

  have hqInt : IsIntegral ℤ q := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C k,
      Polynomial.monic_X_pow_sub_C (R := ℤ) (n := 2) k (show (2 : ℕ) ≠ 0 by decide), ?_⟩
    have hC : Polynomial.eval₂ (Int.castRingHom ℚ) q (Polynomial.C k) = (k : ℚ) := by
      simpa using (Polynomial.eval₂_C (f := Int.castRingHom ℚ) (x := q) (a := k))
    calc
      Polynomial.eval₂ (Int.castRingHom ℚ) q (Polynomial.X ^ 2 - Polynomial.C k)
          = q ^ 2 - Polynomial.eval₂ (Int.castRingHom ℚ) q (Polynomial.C k) := by
            simp [Polynomial.eval₂_sub]
      _ = q ^ 2 - (k : ℚ) := by simpa [hC]
      _ = 0 := by simp [hq2]
  obtain ⟨b', hb'⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).1 hqInt
  have hb'q : (b' : ℚ) = q := by simpa using hb'
  have him : x.im = (b' : ℚ) / 2 := by
    have : (b' : ℚ) = 2 * x.im := by simpa [q] using hb'q
    nlinarith [this]

  have hxHalf : x = Qsqrtd.halfInt d a' b' := by
    ext <;> simp [Qsqrtd.halfInt, hre, him]

  have hnormHalf : (n' : ℚ) = (((a' ^ 2 - d * b' ^ 2 : ℤ) : ℚ) / (4 : ℤ)) := by
    calc
      (n' : ℚ) = Qsqrtd.norm' x := hn'norm
      _ = Qsqrtd.norm' (Qsqrtd.halfInt d a' b') := by simp [hxHalf]
      _ = (a' ^ 2 - (d : ℚ) * b' ^ 2) / 4 := Qsqrtd.norm_halfInt d a' b'
      _ = (((a' ^ 2 - d * b' ^ 2 : ℤ) : ℚ) / (4 : ℤ)) := by norm_num

  have hhalf : (((a' ^ 2 - d * b' ^ 2 : ℤ) : ℚ) / (4 : ℤ)) = (n' : ℚ) := by
    simpa using hnormHalf.symm
  have hden : ((((a' ^ 2 - d * b' ^ 2 : ℤ) : ℚ) / (4 : ℤ)).den = 1) := by
    rw [hhalf]
    simp
  have hdiv : (4 : ℤ) ∣ (a' ^ 2 - d * b' ^ 2) :=
    (Rat.den_div_intCast_eq_one_iff (a' ^ 2 - d * b' ^ 2) 4 (by norm_num)).1 hden

  rcases exists_zquad_image_of_dvd_four_sub_sq_of_ne_one_mod_four d a' b' hd hd4 hdiv with ⟨z, hz⟩
  refine ⟨z, ?_⟩
  simpa [hxHalf] using hz

/-- Forward target for the intermediate path (`d % 4 ≠ 1` branch). -/
lemma ringOfIntegers_equiv_zquad_of_mod_four_ne_one
    (d : ℤ) [IsQuadraticParam d] [NumberField (Qsqrtd d)]
    (hd4 : d % 4 ≠ 1) :
    Nonempty (𝓞 (Qsqrtd d) ≃+* ZQuad d) := by
  letI : Algebra (ZQuad d) (Qsqrtd d) := (toQsqrtd d).toAlgebra
  let hIC : IsIntegralClosure (ZQuad d) ℤ (Qsqrtd d) :=
    { algebraMap_injective := by
        simpa [RingHom.toAlgebra] using (toQsqrtd_injective d)
      isIntegral_iff := by
        intro x
        constructor
        · intro hx
          rcases exists_zquad_of_isIntegral_of_ne_one_mod_four d hd4 hx with ⟨z, hz⟩
          exact ⟨z, by simpa [RingHom.toAlgebra] using hz⟩
        · rintro ⟨z, rfl⟩
          simpa [RingHom.toAlgebra] using (isIntegral_toQsqrtd d z) }
  exact ⟨@NumberField.RingOfIntegers.equiv (Qsqrtd d)
    (inferInstance : Field (Qsqrtd d))
    (ZQuad d)
    (inferInstance : CommRing (ZQuad d))
    ((toQsqrtd d).toAlgebra)
    hIC⟩

end ZQuad

end ClassificationOfIntegersOfQuadraticNumberFields
