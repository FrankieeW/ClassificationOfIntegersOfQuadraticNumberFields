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
- [ ] Add bridge lemmas to half-integer normal form with same-parity criterion.
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

/-- Candidate carrier set of `ℤ[(1 + √(1 + 4d))/2]` inside `Q(√(1 + 4d))`. -/
def carrierSet (d : ℤ) : Set (Qsqrtd (qParam d)) := Set.range (toQsqrtdFun d)

end ZOnePlusSqrtOverTwo
