# Blueprint: Classification of Integers of Quadratic Number Fields

## Overview

This project formalizes the classification of rings of integers in
quadratic number fields Q(√d) in Lean 4 with Mathlib, following
George Boxer's algebraic number theory lecture notes.

**Main theorem**: For squarefree d ∉ {0,1},

```
         ⎧ ℤ[√d]           if d ≢ 1 (mod 4)
𝓞_d  ≅  ⎨
         ⎩ ℤ[(1+√d)/2]     if d ≡ 1 (mod 4)
```

---

## Part I: Completed

### Chapter 1 — Quadratic Number Fields

| Item | Lean declaration | Status |
|------|-----------------|--------|
| Quadratic field parameter | `QuadFieldParam` | done |
| Quadratic algebra Q(√d) | `Qsqrtd` | done |
| Field instance | `QuadNumberField` | done |
| Trace = 2·re | `trace_eq_two_re` | done |
| Norm = re² − d·im² | `norm_eq_sqr_minus_d_sqr` | done |
| Rescaling Q(√d) ≅ Q(√(a²d)) | `Qsqrtd.rescale` | done |
| Parameter rigidity (d₁ ≠ d₂ ⟹ non-iso) | `quadratic_field_param_unique` | done |

### Chapter 2 — Integrality Criteria

| Item | Lean declaration | Status |
|------|-----------------|--------|
| Half-integer element | `halfInt` | done |
| Trace of halfInt | `trace_halfInt` | done |
| Norm of halfInt | `norm_halfInt` | done |
| Integral ⟹ half-integer + 4∣(a'²−d·b'²) | `exists_halfInt_with_div_four_of_isIntegral` | done |
| Mod-4 dichotomy (both-even ∨ both-odd+d≡1) | `dvd_four_sub_sq_iff_even_even_or_odd_odd_mod_four_one` | done |
| d ≢ 1: both even | `dvd_four_sub_sq_iff_even_even_of_ne_one_mod_four` | done |
| d ≡ 1: same parity | `dvd_four_sub_sq_iff_same_parity_of_one_mod_four` | done |
| d ≢ 1 branch: integral ∈ ℤ[√d] | `exists_zsqrtd_of_isIntegral_of_ne_one_mod_four` | done |
| d ≡ 1 branch: integral ∈ ℤ[(1+√d)/2] | `exists_zOnePlusSqrtOverTwo_of_isIntegral_of_one_mod_four` | done |

### Chapter 3 — Ring of Integers Classification

| Item | Lean declaration | Status |
|------|-----------------|--------|
| ℤ[√d] ring model | `Zsqrtd` | done |
| ℤ[(1+√d)/2] ring model | `ZOnePlusSqrtOverTwo` | done |
| d ≢ 1 ⟹ 𝓞 ≅ ℤ[√d] | `ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one` | done |
| d ≡ 1 ⟹ 𝓞 ≅ ℤ[(1+√d)/2] | `ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one` | done |
| **Main classification** | `ringOfIntegers_classification` | **done** |

---

## Part II: Planned

### Chapter 4 — Integral Basis (Boxer Lecture 5)

> Goal: Extract an explicit ℤ-basis for 𝓞_d from the classification.

| Item | Depends on | Status |
|------|-----------|--------|
| 𝓞_d is free ℤ-module of rank 2 | Ch.3 classification | planned |
| Basis {1, √d} when d ≢ 1 (mod 4) | branch theorem | planned |
| Basis {1, (1+√d)/2} when d ≡ 1 (mod 4) | branch theorem | planned |
| Unified basis {1, ω_d} | both branches | planned |

**Lean strategy**: Transport canonical ℤ²-basis through ring iso
via `Basis.map` / `LinearEquiv.ofBijective`.

### Chapter 5 — Discriminant (Boxer Lecture 6)

> Goal: Compute disc(𝓞_d) in both branches.

| Item | Depends on | Status |
|------|-----------|--------|
| Discriminant definition via trace matrix | integral basis | planned |
| disc = 4d when d ≢ 1 (mod 4) | basis {1,√d} | planned |
| disc = d when d ≡ 1 (mod 4) | basis {1,(1+√d)/2} | planned |

**Lean strategy**: Evaluate `Algebra.discr ℤ B` for explicit basis `B`,
reduce to arithmetic via `ring` / `norm_num`.

### Chapter 6 — Norm Multiplicativity (Boxer Lecture 3)

> Goal: Formalize N(αβ) = N(α)N(β) and consequences.

| Item | Depends on | Status |
|------|-----------|--------|
| N(xy) = N(x)N(y) | trace/norm defs | planned |
| α ∈ 𝓞 ⟹ N(α) ∈ ℤ | classification | planned |
| α ∈ 𝓞× ⟺ N(α) = ±1 | norm integrality | planned |
| Explicit norm formulas per branch | ring models | planned |

**Lean strategy**: Multiplicativity by `ext` + `ring`.
Unit criterion from `Algebra.norm_eq_prod_automorphisms`.

### Chapter 7 — Ideals and Dedekind Domains (Boxer Lectures 8–17)

> Goal (long-term): Ideal theory and prime splitting in 𝓞_d.

| Item | Depends on | Status |
|------|-----------|--------|
| 𝓞_d is Dedekind domain | classification | planned |
| Unique factorization into prime ideals | Dedekind | planned |
| Splitting criterion (Legendre symbol) | discriminant | planned |
| Class group / class number | ideal factorization | planned |

**Lean strategy**: Transport `IsDedekindDomain` from Mathlib's
`NumberField.RingOfIntegers` through the ring isomorphism.

---

## Module Dependency Graph

```
QuadNumberField/
├── Basic.lean          ← Qsqrtd, trace, norm
├── Param.lean          ← QuadFieldParam
├── FieldInstance.lean   ← Field instance
├── Rescale.lean        ← Rescaling isomorphisms
├── ParamUniqueness.lean ← Parameter rigidity
└── RingOfIntegers/
    ├── HalfInt.lean      ← halfInt, trace/norm formulas
    ├── ModFour.lean      ← mod-4 parity criteria
    ├── Zsqrtd.lean       ← ℤ[√d] model + embedding
    ├── ZOnePlusSqrtOverTwo.lean ← ℤ[(1+√d)/2] model
    ├── Integrality.lean  ← integrality characterization
    └── Classification.lean ← ★ main classification theorem
```

---

## References

- George Boxer, *Algebraic Number Theory* lecture notes (Lectures 1–17)
- Mathlib: `Mathlib.NumberTheory.NumberField.RingOfIntegers`,
  `Mathlib.RingTheory.DedekindDomain`
