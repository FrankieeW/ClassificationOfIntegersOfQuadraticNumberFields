/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadNumberField.RingOfIntegers.HalfInt

/-!
# `ℤ[(1 + √(1 + 4k)) / 2]`
# `ℤ[(1 + √d) / 2]`

This file packages the standard order candidate in the `d ≡ 1 [ZMOD 4]` branch.

## TODO (Revised)

1. Parameter semantics and core embedding
- [x] Keep the model
  `ZOnePlusSqrtOverTwo k := QuadraticAlgebra ℤ 1 k` (`ω^2 = ω + k`).
- [ ] Treat argument as `k`; ambient field parameter is `d = 1 + 4 * k`.
- [ ] Upgrade `toQsqrtdFun` to a ring hom into `Q(√(1 + 4*k))`.

2. Generator and defining equation
- [ ] Define canonical generator `ω : ZOnePlusSqrtOverTwo k`.
- [ ] Prove `ω^2 = ω + k`.
- [ ] Add compatibility lemma with `(1 + √(1 + 4*k)) / 2` in `Q(√(1 + 4*k))`.

3. Classification interfaces
- [ ] Package a branch target carrier (`Subring`/`Subalgebra`) for `d % 4 = 1`.
- [x] Add bridge lemmas to half-integer normal form with same-parity criterion.
- [ ] Expose theorem names consumed by `Integrality.lean` and `Classification.lean`.
-/

namespace Qsqrtd

/-- The discriminant-like parameter `1 + 4k` viewed in `ℚ`. -/
abbrev d_of_k (k : ℤ) : ℚ := ((1 + 4 * k : ℤ) : ℚ)

/-- `ω_k = (1 + √(1 + 4k)) / 2` in `Q(√(1 + 4k))`. -/
def omega (k : ℤ) : Qsqrtd (d_of_k k) := ⟨(1 / 2 : ℚ), (1 / 2 : ℚ)⟩

/-- The order candidate `ℤ[ω_k]` with `ω_k = (1 + √(1 + 4k)) / 2`. -/
abbrev Zomega (k : ℤ) : Subalgebra ℤ (Qsqrtd (d_of_k k)) :=
  Algebra.adjoin ℤ ({omega k} : Set (Qsqrtd (d_of_k k)))

lemma omega_mem_Zomega (k : ℤ) : omega k ∈ Zomega k := by
  exact Algebra.subset_adjoin (by simp)

end Qsqrtd

/-- Algebraic model of `ℤ[(1 + √(1 + 4d))/2]` via `ω^2 = ω + d`. -/
abbrev ZOnePlusSqrtOverTwo (d : ℤ) : Type := QuadraticAlgebra ℤ 1 d

namespace ZOnePlusSqrtOverTwo

/-- Ambient parameter in `ℚ`: `1 + 4d`. -/
abbrev qParam (d : ℤ) : ℚ := Qsqrtd.d_of_k d

/-- Coordinate-level embedding candidate into `Q(√(1 + 4d))`. -/
def toQsqrtdFun (d : ℤ) : ZOnePlusSqrtOverTwo d → Qsqrtd (qParam d) :=
  fun x => ⟨x.re + x.im / 2, x.im / 2⟩

/-- Coordinate-level embedding as a ring hom into `Q(√(1 + 4d))`. -/
def toQsqrtdHom (d : ℤ) : ZOnePlusSqrtOverTwo d →+* Qsqrtd (qParam d) where
  toFun := toQsqrtdFun d
  map_one' := by
    have hre : (1 : ZOnePlusSqrtOverTwo d).re = 1 := rfl
    have him : (1 : ZOnePlusSqrtOverTwo d).im = 0 := rfl
    ext <;> simp [toQsqrtdFun, hre, him]
  map_mul' := by
    intro x y
    ext <;> simp [toQsqrtdFun, qParam, Qsqrtd.d_of_k, QuadraticAlgebra.mk_mul_mk] <;>
      norm_num <;> ring_nf
  map_zero' := by
    have hre : (0 : ZOnePlusSqrtOverTwo d).re = 0 := rfl
    have him : (0 : ZOnePlusSqrtOverTwo d).im = 0 := rfl
    ext <;> simp [toQsqrtdFun, hre, him]
  map_add' := by
    intro x y
    ext <;> simp [toQsqrtdFun] <;> norm_num <;> ring_nf

/-- Candidate carrier set of `ℤ[(1 + √(1 + 4d))/2]` inside `Q(√(1 + 4d))`. -/
def carrierSet (d : ℤ) : Set (Qsqrtd (qParam d)) := Set.range (toQsqrtdFun d)

/-- A half-integer element belongs to the `ℤ[(1 + √(1+4k))/2]` carrier iff the two
numerators have the same parity. -/
theorem halfInt_mem_carrierSet_iff_same_parity (k a' b' : ℤ) :
    (∃ z : ZOnePlusSqrtOverTwo k,
      toQsqrtdFun k z = QuadNumberField.RingOfIntegers.halfInt (1 + 4 * k) a' b') ↔
      a' % 2 = b' % 2 := by
  constructor
  · rintro ⟨z, hz⟩
    have him : z.im / 2 = (b' : ℚ) / 2 := by
      simpa [toQsqrtdFun, QuadNumberField.RingOfIntegers.halfInt] using
        congrArg QuadraticAlgebra.im hz
    have hbq : z.im = (b' : ℚ) := by
      nlinarith [him]
    have hreq : z.re + z.im / 2 = (a' : ℚ) / 2 := by
      simpa [toQsqrtdFun, QuadNumberField.RingOfIntegers.halfInt] using
        congrArg QuadraticAlgebra.re hz
    have haq : 2 * z.re + z.im = (a' : ℚ) := by
      nlinarith [hreq]
    have ha : 2 * z.re + z.im = a' := by exact_mod_cast haq
    have hb : z.im = b' := by exact_mod_cast hbq
    have ha' : 2 * z.re + b' = a' := by simpa [hb] using ha
    omega
  · intro hpar
    have hmod : (a' - b') % 2 = 0 := by
      omega
    have hdiv : (2 : ℤ) ∣ (a' - b') := Int.dvd_iff_emod_eq_zero.mpr hmod
    rcases hdiv with ⟨t, ht⟩
    have hrepr : a' = 2 * t + b' := by
      omega
    refine ⟨⟨t, b'⟩, ?_⟩
    ext
    · simp [toQsqrtdFun, QuadNumberField.RingOfIntegers.halfInt, hrepr]
      ring
    · simp [toQsqrtdFun, QuadNumberField.RingOfIntegers.halfInt]

/-- Equivalent set-membership form of `halfInt_mem_carrierSet_iff_same_parity`. -/
theorem halfInt_mem_carrierSet_iff_same_parity_set (k a' b' : ℤ) :
    QuadNumberField.RingOfIntegers.halfInt (1 + 4 * k) a' b' ∈ carrierSet k ↔
      a' % 2 = b' % 2 := by
  simpa [carrierSet] using (halfInt_mem_carrierSet_iff_same_parity k a' b')

end ZOnePlusSqrtOverTwo
