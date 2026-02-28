/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import Mathlib.Algebra.QuadraticAlgebra.Defs
import Mathlib.Algebra.Squarefree.Basic




class QuadFieldParam (d : ℤ) : Prop where
  squarefree : Squarefree d
  ne_zero : d ≠ 0
  ne_one : d ≠ 1


abbrev Qsqrtd (d : ℚ) : Type := QuadraticAlgebra ℚ d 0

abbrev QuadNumberField (d : ℤ) [QuadFieldParam d] : Type := Qsqrtd (d : ℚ)

--Qsqrtd 0 iso to ℚ, so not a quadratic extension
def Qsqrtd_zero_iso_rat : Qsqrtd 0 ≃ₐ[ℚ] ℚ := by
  -- 构造同构
  have h1 : (1 : Qsqrtd 0) = ⟨1, 0⟩ := by ext <;> rfl
  exact AlgEquiv.ofLinearEquiv
    { toFun := fun x => x.re
      invFun := fun r => ⟨r, 0⟩
      map_add' := by simp
      map_smul' := by simp
      left_inv := by
        sorry
      right_inv := sorry
    }
    (by simp [h1])
    (by sorry)
instance {d : ℤ} [QuadFieldParam d] : Field (QuadNumberField d) := by
  sorry
