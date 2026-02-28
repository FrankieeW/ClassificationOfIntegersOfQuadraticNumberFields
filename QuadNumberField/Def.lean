/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import Mathlib.Algebra.QuadraticAlgebra.Defs
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Tactic





abbrev Qsqrtd (d : ℚ) : Type := QuadraticAlgebra ℚ d 0


-- ¬ IsReduced Qsqrtd 0
-- 不是约化环（存在 ε ≠ 0 且 ε^2 = 0）
lemma Qsqrtd_zero_not_isReduced : ¬ IsReduced (Qsqrtd (0 : ℚ)) := by
  rintro ⟨h⟩
  sorry

lemma Qsqrtd_one_not_isField : ¬ IsField (Qsqrtd (1 : ℚ)) := by
  rintro ⟨h⟩
  sorry
-- Squarefree 构造同构
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
-- Q 通过 rescale 可以化为整数参数
--
class QuadFieldParam (d : ℤ) : Prop where
  squarefree : Squarefree d
  ne_zero : d ≠ 0
  ne_one : d ≠ 1
--
abbrev QuadNumberField (d : ℤ) [QuadFieldParam d] : Type := Qsqrtd (d : ℚ)

instance {d : ℤ} [QuadFieldParam d] : Field (QuadNumberField d) := by
  sorry
