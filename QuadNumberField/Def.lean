/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Tactic
import Init.Data.Rat.Basic




abbrev Qsqrtd (d : ℚ) : Type := QuadraticAlgebra ℚ d 0


-- ¬ IsReduced Qsqrtd 0
-- 不是约化环（存在 ε ≠ 0 且 ε^2 = 0）
lemma Qsqrtd_zero_not_isReduced : ¬ IsReduced (Qsqrtd (0 : ℚ)) := by
  intro ⟨h⟩
  have hnil : IsNilpotent (⟨0, 1⟩ : Qsqrtd 0) :=
    ⟨2, by ext <;> simp [pow_succ, pow_zero, QuadraticAlgebra.mk_mul_mk]⟩
  have hne : (⟨0, 1⟩ : Qsqrtd 0) ≠ 0 := by
    intro heq; exact one_ne_zero (congr_arg QuadraticAlgebra.im heq)
  exact hne (h _ hnil)

-- Squarefree
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

-- d ∈ ℚ can be rescaled into ℤ
theorem Qsqrtd_iso_int_param (d : ℚ) :
    ∃ z : ℤ, Nonempty (Qsqrtd d ≃ₐ[ℚ] Qsqrtd (z : ℚ)) := by
  -- d = m/n, then Qsqrtd (m/n) ≃ₐ[ℚ] Qsqrtd (m*n) via rescale with a = n
  obtain ⟨m, n, hn0, hd⟩ : ∃ m n : ℤ, n ≠ 0 ∧ d = m / n := by
    have hd := ne_of_gt (Rat.den_pos d)
    exact ⟨d.num, d.den, Int.ofNat_ne_zero.mpr hd, (Rat.num_div_den d).symm⟩
  use m * n
  have ha : (n : ℚ) ≠ 0 := by exact_mod_cast hn0
  have hrescale : Qsqrtd d ≃ₐ[ℚ] Qsqrtd (n ^ 2 * d) := rescale d n ha
  have heq : (n : ℚ) ^ 2 * d = m * n := by
    rw [hd]
    field_simp [mul_assoc]
  have hcast : (m * n : ℚ) = (m * n : ℤ) := (Int.cast_mul m n).symm
  exact ⟨hrescale.trans (AlgEquiv.cast (by rw [heq, hcast]))⟩

-- non squarefree d can be rescaled into squarefree (d ≠ 0)
theorem Qsqrtd_iso_squarefree_int_param {d : ℤ} (hd : d ≠ 0) :
    ∃ z : ℤ, Squarefree z ∧ Nonempty (Qsqrtd (d : ℚ) ≃ₐ[ℚ] Qsqrtd (z : ℚ)) := by
  -- Factor |d| = b² * a where a is squarefree
  obtain ⟨a, b, heq, ha⟩ := Nat.sq_mul_squarefree d.natAbs
  -- b ≠ 0 since d ≠ 0
  have hb : b ≠ 0 := by
    intro hb; subst hb; simp at heq
    exact hd (Int.natAbs_eq_zero.mp heq.symm)
  -- z = sign(d) * a is our squarefree target
  refine ⟨d.sign * ↑a, ?_, ?_⟩
  · -- Squarefree (d.sign * ↑a)
    rw [← Int.squarefree_natAbs]
    rwa [Int.natAbs_mul, Int.natAbs_sign_of_ne_zero hd, Int.natAbs_natCast, one_mul]
  · -- Isomorphism via rescale by b⁻¹
    have hbQ : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hb
    have hrescale := rescale (↑d) (↑b)⁻¹ (inv_ne_zero hbQ)
    -- d = sign(d) * b² * a as integers
    have hd_int : d = d.sign * (↑b ^ 2 * ↑a) := by
      conv_lhs => rw [(Int.sign_mul_natAbs d).symm]
      congr 1; exact_mod_cast heq.symm
    -- Key equation: b⁻² * d = sign(d) * a
    have hkey : ((↑b : ℚ)⁻¹) ^ 2 * (↑d : ℚ) = ↑(d.sign * (↑a : ℤ)) := by
      have hd_rat : (d : ℚ) = (d.sign : ℚ) * ((b : ℚ) ^ 2 * (a : ℚ)) := by
        exact_mod_cast hd_int
      rw [hd_rat]; field_simp; push_cast; rfl
    exact ⟨hrescale.trans
      (AlgEquiv.cast (A := fun d => QuadraticAlgebra ℚ d 0) hkey)⟩

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
  -- (1 + √1)(1 - √1) = 1 - 1 = 0, but both factors are nonzero
  haveI := hF.isDomain
  have hprod : (⟨1, 1⟩ : Qsqrtd 1) * ⟨1, -1⟩ = 0 := by
    ext <;> simp [QuadraticAlgebra.mk_mul_mk]
  have hne : (⟨1, 1⟩ : Qsqrtd 1) ≠ 0 := by
    intro h; exact one_ne_zero (congr_arg QuadraticAlgebra.re h)
  have hne' : (⟨1, -1⟩ : Qsqrtd 1) ≠ 0 := by
    intro h; exact one_ne_zero (congr_arg QuadraticAlgebra.re h)
  rcases mul_eq_zero.mp hprod with h | h <;> contradiction

abbrev QuadNumberField (d : ℤ) [QuadFieldParam d] : Type := Qsqrtd (d : ℚ)

instance {d : ℤ} [QuadFieldParam d] : Field (QuadNumberField d) := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r) := ⟨by
    intro r hr
    have hsqQ : IsSquare ((d : ℤ) : ℚ) := ⟨r, by nlinarith [hr]⟩
    exact (not_isSquare_int d) (Rat.isSquare_intCast_iff.mp hsqQ)
  ⟩
  infer_instance
