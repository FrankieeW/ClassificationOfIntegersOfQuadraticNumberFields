/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Tactic
import QuadNumberField.Basic

lemma Qsqrtd_zero_not_isReduced : ¬ IsReduced (Qsqrtd (0 : ℚ)) := by
  intro ⟨h⟩
  have hnil : IsNilpotent (⟨0, 1⟩ : Qsqrtd 0) :=
    ⟨2, by ext <;> simp [pow_succ, pow_zero, QuadraticAlgebra.mk_mul_mk]⟩
  have hne : (⟨0, 1⟩ : Qsqrtd 0) ≠ 0 := by
    intro heq; exact one_ne_zero (congr_arg QuadraticAlgebra.im heq)
  exact hne (h _ hnil)

lemma Qsqrtd_zero_not_isField : ¬ IsField (Qsqrtd (0 : ℚ)) := by
  intro hF
  haveI := hF.isDomain
  exact Qsqrtd_zero_not_isReduced (inferInstance : IsReduced (Qsqrtd (0 : ℚ)))

class QuadFieldParam (d : ℤ) : Prop where
  squarefree : Squarefree d
  ne_zero : d ≠ 0
  ne_one : d ≠ 1

lemma not_isSquare_int (d : ℤ) [QuadFieldParam d] : ¬ IsSquare d := by
  intro hdSq
  rcases hdSq with ⟨z, hz⟩
  by_cases huz : IsUnit z
  · rcases Int.isUnit_iff.mp huz with hz1 | hz1
    · have : d = 1 := by simpa [hz1] using hz
      exact (QuadFieldParam.ne_one (d := d)) this
    · have : d = 1 := by simpa [hz1] using hz
      exact (QuadFieldParam.ne_one (d := d)) this
  · have hsqz2 : Squarefree (z ^ 2) := by
      simpa [hz, pow_two] using (QuadFieldParam.squarefree (d := d))
    have h01 : (2 : ℕ) = 0 ∨ (2 : ℕ) = 1 :=
      Squarefree.eq_zero_or_one_of_pow_of_not_isUnit (x := z) (n := 2) hsqz2 huz
    norm_num at h01

lemma Qsqrtd_one_not_isField : ¬ IsField (Qsqrtd (1 : ℚ)) := by
  intro hF
  haveI := hF.isDomain
  have hprod : (⟨1, 1⟩ : Qsqrtd 1) * ⟨1, -1⟩ = 0 := by
    ext <;> simp [QuadraticAlgebra.mk_mul_mk]
  have hne : (⟨1, 1⟩ : Qsqrtd 1) ≠ 0 := by
    intro h; exact one_ne_zero (congr_arg QuadraticAlgebra.re h)
  have hne' : (⟨1, -1⟩ : Qsqrtd 1) ≠ 0 := by
    intro h; exact one_ne_zero (congr_arg QuadraticAlgebra.re h)
  rcases mul_eq_zero.mp hprod with h | h <;> contradiction
