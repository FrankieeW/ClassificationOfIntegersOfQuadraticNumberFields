/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadNumberField.Param

abbrev QuadNumberField (d : ℤ) [QuadFieldParam d] : Type := Qsqrtd (d : ℚ)

instance {d : ℤ} [QuadFieldParam d] : Field (QuadNumberField d) := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r) := ⟨by
    intro r hr
    have hsqQ : IsSquare ((d : ℤ) : ℚ) := ⟨r, by nlinarith [hr]⟩
    exact (not_isSquare_int d) (Rat.isSquare_intCast_iff.mp hsqQ)
  ⟩
  infer_instance

