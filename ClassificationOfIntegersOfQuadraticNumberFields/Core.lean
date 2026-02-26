import Mathlib
-- Reference: doc/tex/George Boxer Notes - NO SOLUTIONS.pdf, §2.1 (page 7)
namespace ClassificationOfIntegersOfQuadraticNumberFields

/-!
## §2.1 Quadratic integer rings — canonical parameters

A quadratic field is `ℚ(√d) = {a + b√d | a, b ∈ ℚ}` for some `d ∈ ℚ×`.
We restrict `d` to **squarefree integers ≠ 0, 1** for three reasons:

1. **`d ≠ 0`**: otherwise `√d = 0` and `ℚ(√0) = ℚ`, not a quadratic extension.
2. **`d ≠ 1`**: otherwise `√1 = 1 ∈ ℚ` and `ℚ(√1) = ℚ`, again trivial.
3. **`Squarefree d`**: for any `a ∈ ℚ×` we have `ℚ(√d) = ℚ(√(a²d))`, so every
   quadratic field has a unique squarefree integer representative. This is the
   content of Exercise 2.4: squarefree integers `d₁ ≠ d₂` give non-isomorphic
   fields `ℚ(√d₁) ≇ ℚ(√d₂)` (proved below as `quadratic_fields_not_iso`).

Together these conditions make `IsQuadraticParam d` exactly the standard
canonical form for quadratic field parameters.

### Proof strategy (how each field is used)

* `ne_one` + `squarefree` ⟹ `d` is not a perfect square in `ℤ`
  (`not_isSquare_int`): if `d = z²` and `z` is a unit then `d = 1`
  (contradicts `ne_one`); if `z` is not a unit then `z²` cannot be
  squarefree (contradicts `squarefree`).

* Not a square in `ℤ` ⟹ not a square in `ℚ` (`IsNonsquareRat`),
  which makes `ℚ(√d)` genuinely a degree-2 extension, hence a `Field`.
-/

/-- Parameters for quadratic fields `ℚ(√d)`: nonzero, nontrivial, and squarefree.

See the module docstring above for the mathematical motivation from Boxer §2.1. -/
class IsQuadraticParam (d : ℤ) : Prop where
  /-- `d ≠ 0` `d ≠ 1`ensures `ℚ(√d)` is not just `ℚ`. -/
  ne_zero : d ≠ 0
  ne_one : d ≠ 1
  /-- `Squarefree d` gives a canonical representative: `ℚ(√d) = ℚ(√(a²d))` for any
  `a ∈ ℚ×`, so we may assume `d` has no repeated prime factors. -/
  squarefree : Squarefree d

/-- The ambient type `Q(√d)`. -/
abbrev Qsqrtd (d : ℤ) : Type := QuadraticAlgebra ℚ (d : ℚ) 0

namespace Qsqrtd

/-- `ℚ(√d) ≃ₐ[ℚ] ℚ(√(a²d))` via `⟨r, s⟩ ↦ ⟨r, s·a⁻¹⟩`.
This shows that rescaling `d` by a nonzero rational square does not change
the quadratic field, which is why we may restrict to squarefree parameters. -/
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

/-- Norm on `Qsqrtd d` with dot notation `x.norm`. -/
abbrev norm {d : ℤ} (x : Qsqrtd d) : ℚ := QuadraticAlgebra.norm x

/-- Trace on `Qsqrtd d` with dot notation `x.trace`. -/
abbrev trace {d : ℤ} (x : Qsqrtd d) : ℚ := x.re + (star x).re

class IsNonsquareRat (d : ℤ) : Prop where
  nonsquare : ∀ r : ℚ, r ^ 2 ≠ (d : ℚ)

/-- A squarefree nontrivial integer parameter is not a square in `ℤ`. -/
lemma not_isSquare_int (d : ℤ) [IsQuadraticParam d] : ¬ IsSquare d := by
  intro hdSq
  rcases hdSq with ⟨z, hz⟩
  by_cases huz : IsUnit z
  · rcases Int.isUnit_iff.mp huz with hz1 | hz1
    · have : d = 1 := by simpa [hz1] using hz
      exact (IsQuadraticParam.ne_one (d := d)) this
    · have : d = 1 := by simpa [hz1] using hz
      exact (IsQuadraticParam.ne_one (d := d)) this
  · have hsqz2 : Squarefree (z ^ 2) := by
      simpa [hz, pow_two] using (IsQuadraticParam.squarefree (d := d))
    have h01 : (2 : ℕ) = 0 ∨ (2 : ℕ) = 1 :=
      Squarefree.eq_zero_or_one_of_pow_of_not_isUnit (x := z) (n := 2) hsqz2 huz
    norm_num at h01

instance (d : ℤ) [IsQuadraticParam d] : IsNonsquareRat d := by
  refine ⟨?_⟩
  intro r hr
  have hsqQ : IsSquare ((d : ℤ) : ℚ) := ⟨r, by simpa [pow_two] using hr.symm⟩
  have hsqZ : IsSquare d := (Rat.isSquare_intCast_iff).1 hsqQ
  exact (not_isSquare_int d) hsqZ

instance {d : ℤ} [IsNonsquareRat d] : Field (Qsqrtd d) := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r) := ⟨by
    intro r hr
    exact (IsNonsquareRat.nonsquare (d := d) r) (by simpa [zero_mul, add_zero] using hr)
  ⟩
  infer_instance

-- Exercise 2.4 (first part): `Q(√d)` is not equivalent to `ℚ` over `ℚ`.


/-- `-1` is not a square in `ℚ`. -/
lemma not_isSquare_neg_one_rat : ¬ IsSquare (- (1 : ℚ)) := by
  rintro ⟨r, hr⟩
  have hnonneg : 0 ≤ r ^ 2 := sq_nonneg r
  nlinarith [hr, hnonneg]

/-- If `m : ℕ` is squarefree as an integer and is a square in `ℤ`, then `m = 1`. -/
lemma nat_eq_one_of_squarefree_intcast_of_isSquare (m : ℕ)
    (hsm : Squarefree (m : ℤ)) (hsq : IsSquare (m : ℤ)) : m = 1 := by
  rcases hsq with ⟨z, hz⟩
  by_cases huz : IsUnit z
  · rcases Int.isUnit_iff.mp huz with hz1 | hz1
    · have hmz : (m : ℤ) = 1 := by simpa [hz1] using hz
      norm_num at hmz
      exact hmz
    · have hmz : (m : ℤ) = 1 := by simpa [hz1] using hz
      norm_num at hmz
      exact hmz
  · have hsqz2 : Squarefree (z ^ 2) := by simpa [hz, pow_two] using hsm
    have h01 : (2 : ℕ) = 0 ∨ (2 : ℕ) = 1 :=
      Squarefree.eq_zero_or_one_of_pow_of_not_isUnit (x := z) (n := 2) hsqz2 huz
    norm_num at h01

/-- If `d₂` is squarefree/nonzero and `d₁ / d₂` is a square in `ℚ`, then `d₂ ∣ d₁`. -/
lemma int_dvd_of_ratio_square (d₁ d₂ : ℤ) (hd₂ : d₂ ≠ 0)
    (hsq_d₂ : Squarefree d₂) (hr : IsSquare ((d₁ : ℚ) / (d₂ : ℚ))) : d₂ ∣ d₁ := by
  have hsq_den_nat : IsSquare (((d₁ : ℚ) / (d₂ : ℚ)).den) := (Rat.isSquare_iff.mp hr).2
  have hsq_den_int : IsSquare ((((d₁ : ℚ) / (d₂ : ℚ)).den : ℤ)) := by
    rcases hsq_den_nat with ⟨n, hn⟩
    refine ⟨(n : ℤ), by exact_mod_cast hn⟩
  have hden_dvd : ((((d₁ : ℚ) / (d₂ : ℚ)).den : ℤ)) ∣ d₂ := by
    simpa [← Rat.divInt_eq_div] using (Rat.den_dvd d₁ d₂)
  have hsqf_den_int : Squarefree ((((d₁ : ℚ) / (d₂ : ℚ)).den : ℤ)) :=
    Squarefree.squarefree_of_dvd hden_dvd hsq_d₂
  have hden1_nat : ((d₁ : ℚ) / (d₂ : ℚ)).den = 1 :=
    nat_eq_one_of_squarefree_intcast_of_isSquare _ hsqf_den_int hsq_den_int
  exact (Rat.den_div_intCast_eq_one_iff d₁ d₂ hd₂).1 hden1_nat

theorem quadratic_fields_not_iso
    (d1 d2 : ℤ) [IsQuadraticParam d1] [IsQuadraticParam d2]
    (hneq : d1 ≠ d2) :
    ¬ Nonempty (Qsqrtd d1 ≃ₐ[ℚ] Qsqrtd d2) := by
  rintro ⟨e⟩
  let x : Qsqrtd d2 := e ⟨0, 1⟩
  have hx : x * x = (d1 : Qsqrtd d2) := by
    change e ⟨0, 1⟩ * e ⟨0, 1⟩ = (d1 : Qsqrtd d2)
    calc
      e ⟨0, 1⟩ * e ⟨0, 1⟩ = e ((⟨0, 1⟩ : Qsqrtd d1) * ⟨0, 1⟩) := by
        symm
        exact e.map_mul _ _
      _ = e (d1 : Qsqrtd d1) := by
        congr 1
        ext <;> simp [Qsqrtd]
      _ = (d1 : Qsqrtd d2) := by simp
  have him0 : (x * x).im = 0 := by
    have him := congrArg QuadraticAlgebra.im hx
    simpa [Qsqrtd] using him
  have hsum : x.re * x.im + x.im * x.re = 0 := by
    simpa [Qsqrtd, mul_assoc, mul_comm, mul_left_comm] using him0
  have hprod : x.re * x.im = 0 := by nlinarith [hsum]
  have hratio : IsSquare ((d1 : ℚ) / (d2 : ℚ)) := by
    rcases mul_eq_zero.mp hprod with hre | him
    · refine ⟨x.im, ?_⟩
      have hre0 : (x * x).re = d1 := by
        have hre' := congrArg QuadraticAlgebra.re hx
        simpa [Qsqrtd] using hre'
      have hmain : (d2 : ℚ) * (x.im ^ 2) = d1 := by
        simpa [Qsqrtd, hre, pow_two, mul_assoc, mul_comm, mul_left_comm] using hre0
      have hd2Q : (d2 : ℚ) ≠ 0 := by
        exact_mod_cast (IsQuadraticParam.ne_zero (d := d2))
      calc
        (d1 : ℚ) / (d2 : ℚ) = (((d2 : ℚ) * (x.im ^ 2)) / (d2 : ℚ)) := by simp [hmain]
        _ = x.im ^ 2 := by field_simp [hd2Q]
        _ = x.im * x.im := by ring
    · exfalso
      have hre0 : (x * x).re = d1 := by
        have hre' := congrArg QuadraticAlgebra.re hx
        simpa [Qsqrtd] using hre'
      have hmain : x.re ^ 2 = d1 := by
        simpa [Qsqrtd, him, pow_two, mul_assoc, mul_comm, mul_left_comm] using hre0
      exact (IsNonsquareRat.nonsquare (d := d1) x.re) hmain
  have hd1 : d1 ≠ 0 := IsQuadraticParam.ne_zero (d := d1)
  have hd2 : d2 ≠ 0 := IsQuadraticParam.ne_zero (d := d2)
  have hratio' : IsSquare ((d2 : ℚ) / (d1 : ℚ)) := by
    rcases hratio with ⟨r, hr⟩
    refine ⟨r⁻¹, ?_⟩
    have hd1Q : (d1 : ℚ) ≠ 0 := by exact_mod_cast hd1
    have hd2Q : (d2 : ℚ) ≠ 0 := by exact_mod_cast hd2
    have h1 : (r⁻¹ * r⁻¹) = (((d1 : ℚ) / (d2 : ℚ)))⁻¹ := by
      simp [hr]
    calc
      ((d2 : ℚ) / (d1 : ℚ)) = (((d1 : ℚ) / (d2 : ℚ)))⁻¹ := by
        field_simp [hd1Q, hd2Q]
      _ = r⁻¹ * r⁻¹ := h1.symm
  have hd21 : d2 ∣ d1 :=
    int_dvd_of_ratio_square d1 d2 hd2 (IsQuadraticParam.squarefree (d := d2)) hratio
  have hd12 : d1 ∣ d2 :=
    int_dvd_of_ratio_square d2 d1 hd1 (IsQuadraticParam.squarefree (d := d1)) hratio'
  have hassoc : Associated d1 d2 := associated_of_dvd_dvd hd12 hd21
  rcases (Int.associated_iff.mp hassoc) with hEq | hNeg
  · exact hneq hEq
  · have hd2Q : (d2 : ℚ) ≠ 0 := by exact_mod_cast hd2
    have hratio_neg1 : ((d1 : ℚ) / (d2 : ℚ)) = (-1 : ℚ) := by
      rw [hNeg]
      simp
      field_simp [hd2Q]
    have hsq_neg1 : IsSquare (- (1 : ℚ)) := by rwa [hratio_neg1] at hratio
    exact not_isSquare_neg_one_rat hsq_neg1

end Qsqrtd

/-!
## §2.1 Exercise 2.7 — mod 4 case analysis

The key step in classifying the ring of integers 𝒪_d of ℚ(√d) is
determining when `4 ∣ a'² - d·b'²` for integers `a', b'`.

When `d` is squarefree, `d % 4 ≠ 0`, so `d % 4 ∈ {1, 2, 3}`.
A mod-4 analysis then shows that `4 ∣ a'² - d·b'²` exactly when
* `a'` and `b'` are both even, **or**
* `a'` and `b'` are both odd **and** `d ≡ 1 (mod 4)`.

This is the heart of the d ≡ 1 (mod 4) vs d ≢ 1 (mod 4) dichotomy.
-/

section Exercise_2_7

/-- A squarefree integer is not divisible by 4. -/
lemma squarefree_int_not_dvd_four (d : ℤ) (hd : Squarefree d) : ¬ (4 : ℤ) ∣ d := by
  intro h
  have h22 : (2 : ℤ) * 2 ∣ d := by
    obtain ⟨k, hk⟩ := h; exact ⟨k, by omega⟩
  have hunit : IsUnit (2 : ℤ) := hd 2 h22
  exact absurd (Int.isUnit_iff.mp hunit) (by omega)

/-- A squarefree integer has `d % 4 ∈ {1, 2, 3}`. -/
lemma squarefree_int_emod_four (d : ℤ) (hd : Squarefree d) :
    d % 4 = 1 ∨ d % 4 = 2 ∨ d % 4 = 3 := by
  have hnd : ¬ (4 : ℤ) ∣ d := squarefree_int_not_dvd_four d hd
  omega

/-- The square of an even integer is 0 mod 4. -/
lemma Int.sq_emod_four_of_even (n : ℤ) (h : 2 ∣ n) : n ^ 2 % 4 = 0 := by
  obtain ⟨k, rfl⟩ := h
  ring_nf
  omega

/-- The square of an odd integer is 1 mod 4. -/
lemma Int.sq_emod_four_of_odd (n : ℤ) (h : ¬ 2 ∣ n) : n ^ 2 % 4 = 1 := by
  set k := n / 2
  have hk : n = 2 * k + 1 := by omega
  rw [hk]; ring_nf; omega

/-- Auxiliary: reduce `(a'^2 - d * b'^2) % 4` to residues of `a'`, `b'`, `d` mod 4.
    This uses `ring_nf` to expand and `Int.emod_emod_of_dvd` to push `% 4` inward. -/
private lemma div4_iff_mod (a' b' d : ℤ) :
    4 ∣ (a' ^ 2 - d * b' ^ 2) ↔ (a' ^ 2 - d * b' ^ 2) % 4 = 0 := by omega

/-- **Exercise 2.7** (Boxer §2.1). For squarefree `d`, `4 ∣ a'² - d·b'²` iff
either both `a', b'` are even, or both are odd and `d ≡ 1 (mod 4)`. -/
theorem exercise_2_7 (d a' b' : ℤ) (hd : Squarefree d) :
    4 ∣ (a' ^ 2 - d * b' ^ 2) ↔
      (2 ∣ a' ∧ 2 ∣ b') ∨ (¬ 2 ∣ a' ∧ ¬ 2 ∣ b' ∧ d % 4 = 1) := by
  have hd4 := squarefree_int_emod_four d hd
  constructor
  · intro hdvd
    by_cases ha : 2 ∣ a' <;> by_cases hb : 2 ∣ b'
    · exact Or.inl ⟨ha, hb⟩
    · -- a' even, b' odd: impossible
      exfalso
      obtain ⟨p, rfl⟩ := ha
      -- b' = 2q + 1 for some q
      have hbr : b' % 2 = 1 := by omega
      have hb_eq : b' = 2 * (b' / 2) + 1 := by omega
      rw [hb_eq] at hdvd; ring_nf at hdvd
      -- now hdvd : 4 ∣ (some expression involving p, b'/2, d)
      -- reduce d mod 4
      have hd_eq : d = 4 * (d / 4) + d % 4 := by omega
      rw [hd_eq] at hdvd; ring_nf at hdvd
      rcases hd4 with hd1 | hd2 | hd3 <;> omega
    · -- a' odd, b' even: impossible
      exfalso
      obtain ⟨q, rfl⟩ := hb
      have har : a' % 2 = 1 := by omega
      have ha_eq : a' = 2 * (a' / 2) + 1 := by omega
      rw [ha_eq] at hdvd; ring_nf at hdvd
      have hd_eq : d = 4 * (d / 4) + d % 4 := by omega
      rw [hd_eq] at hdvd; ring_nf at hdvd
      rcases hd4 with hd1 | hd2 | hd3 <;> omega
    · -- a' odd, b' odd: must have d ≡ 1 (mod 4)
      right; refine ⟨ha, hb, ?_⟩
      have ha_eq : a' = 2 * (a' / 2) + 1 := by omega
      have hb_eq : b' = 2 * (b' / 2) + 1 := by omega
      rw [ha_eq, hb_eq] at hdvd; ring_nf at hdvd
      have hd_eq : d = 4 * (d / 4) + d % 4 := by omega
      rw [hd_eq] at hdvd; ring_nf at hdvd
      rcases hd4 with hd1 | hd2 | hd3 <;> omega
  · intro h
    rcases h with ⟨ha, hb⟩ | ⟨ha, hb, hd1⟩
    · -- Both even
      obtain ⟨p, rfl⟩ := ha
      obtain ⟨q, rfl⟩ := hb
      exact ⟨p ^ 2 - d * q ^ 2, by ring⟩
    · -- Both odd, d ≡ 1 (mod 4)
      have ha_eq : a' = 2 * (a' / 2) + 1 := by omega
      have hb_eq : b' = 2 * (b' / 2) + 1 := by omega
      rw [ha_eq, hb_eq]; ring_nf
      have hd_eq : d = 4 * (d / 4) + 1 := by omega
      rw [hd_eq]; ring_nf
      omega

/-- When `d ≢ 1 (mod 4)`, `4 ∣ a'² - d·b'²` forces both `a', b'` even. -/
theorem exercise_2_7_not_one_mod_four (d a' b' : ℤ) (hd : Squarefree d)
    (hd4 : d % 4 ≠ 1) (h : 4 ∣ (a' ^ 2 - d * b' ^ 2)) :
    2 ∣ a' ∧ 2 ∣ b' := by
  rcases (exercise_2_7 d a' b' hd).mp h with hab | ⟨_, _, hd1⟩
  · exact hab
  · exact absurd hd1 hd4

/-- When `d ≡ 1 (mod 4)`, `4 ∣ a'² - d·b'²` iff `a' ≡ b' (mod 2)`. -/
theorem exercise_2_7_one_mod_four (d a' b' : ℤ) (hd : Squarefree d)
    (hd4 : d % 4 = 1) :
    4 ∣ (a' ^ 2 - d * b' ^ 2) ↔ a' % 2 = b' % 2 := by
  rw [exercise_2_7 d a' b' hd]
  constructor
  · rintro (⟨ha, hb⟩ | ⟨ha, hb, _⟩) <;> omega
  · intro h
    by_cases ha : 2 ∣ a'
    · left; exact ⟨ha, by omega⟩
    · right; exact ⟨ha, by omega, hd4⟩

end Exercise_2_7

end ClassificationOfIntegersOfQuadraticNumberFields
