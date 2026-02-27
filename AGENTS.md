# AGENTS.md — ClassificationOfIntegersOfQuadraticNumberFields

This file provides guidance for AI agents operating in this Lean 4 theorem proving project.

## Project Overview

**Project Type**: Lean 4 mathematical theorem proving library  
**Lean Version**: v4.29.0-rc2  
**Main Dependency**: mathlib (leanprover-community v4.29.0-rc2)  
**Source Location**: `ClassificationOfIntegersOfQuadraticNumberFields/*.lean`

## Build, Lint, and Test Commands

### Running the Project

```bash
# Fetch dependencies and build cache
lake exe cache get

# Build the full project
lake build

# Clean build artifacts
lake clean

# Type-check a single file (fastest for verification)
lean ClassificationOfIntegersOfQuadraticNumberFields/Core.lean
```

### Running Tests

Lean 4 proofs are verified during compilation—no separate test runner exists.

```bash
# Verify the full project (compiles all proofs)
lake build

# Verify a single file (quick feedback)
lean ClassificationOfIntegersOfQuadraticNumberFields/Core.lean

# Verify a specific module
lean <path-to-module>.lean
```

### Debugging & Diagnostics

```bash
# Full build with detailed output
lake build -v

# Run Lean with trace enabled
lean --trace <path>.lean
```

### LSP Tools (Recommended for AI Agents)

Use Lean LSP tools before and after edits. These are the most important:

| Tool | Purpose |
|------|---------|
| `lean_goal` | See exact proof goal at cursor position |
| `lean_hover_info` | Understand types and get documentation |
| `lean_loogle` | Search mathlib by type signature |
| `lean_leansearch` | Semantic search in mathlib |
| `lean_leanfinder` | Goal-aware semantic search |
| `lean_state_search` | Find lemmas to close current goal |
| `lean_hammer_premeise` | Get premise suggestions for automation |
| `lean_diagnostic_messages` | Get errors/warnings for a file |

### CI Commands

```bash
# Local CI check (same as GitHub Actions)
lake build

# Build with mathlib axioms verification
# (proofs are sound if they only use standard axioms)
```

## Code Style Guidelines

### File Organization

- **Main entry point**: `ClassificationOfIntegersOfQuadraticNumberFields.lean`
- **Core formalization**: `ClassificationOfIntegersOfQuadraticNumberFields/Core.lean`
- **Use namespaces**: `namespace ClassificationOfIntegersOfQuadraticNumberFields`
- **Group related content**: Use `section`/`namespace` with explicit `end`

### Naming Conventions

| Element | Convention | Example |
|---------|------------|---------|
| Files | CamelCase | `Core.lean`, `MinimalPolynomial.lean` |
| Definitions/Theorems/Lemmas | snake_case | `not_isSquare_int` |
| Variables | lowercase | `d`, `d₁`, `d₂`, `x` |
| Type variables | capitals | `R`, `K` |
| **Unicode symbols** | Preferred | `→`, `∀`, `∃`, `↔`, `∈`, `≠`, `⟨⟩` |

### Import Style

```lean
import Mathlib
import ClassificationOfIntegersOfQuadraticNumberFields.Base
import ClassificationOfIntegersOfQuadraticNumberFields.NonIso
```

- Put `Mathlib` first
- Then local imports in dependency order
- Avoid unused imports (Lean will warn)

### Proof Structure

```lean
/-- Statement description. -/
theorem some_theorem
    (h₁ : P)
    (h₂ : Q) :
    R := by
  -- tactics
  sorry
```

### Documentation Standards

- **Docstrings**: Use `/-- ... -/` for definitions, theorems, lemmas
- **Module-level**: Use `/-! ... -/` for section/namespace documentation
- **Keep it brief**: One-line for simple statements, paragraph for complex ones

### Error Handling / Proof Completeness

- **Temporary `sorry`**: Allowed during development
- **Final deliverables**: No `sorry` unless explicitly requested
- ** Axiom checking**: Ensure proofs only use standard axioms (`propext`, `Classical.choice`, `Quot.sound`)

### Lean Options (from `lakefile.toml`)

```toml
[leanOptions]
pp.unicode.fun = true        # Pretty-print Unicode
relaxedAutoImplicit = false  # Strict implicit handling
weak.linter.mathlibStandardSet = true
maxSynthPendingDepth = 3
```

## Lean 4 Skill for AI Agents

**Important**: When working on proofs, load the `lean4` skill for specialized assistance:

- **Prove**: Use `/lean4:prove` for guided cycle-by-cycle theorem proving
- **Autoprove**: Use `/lean4:autoprove` for autonomous multi-cycle proving
- **Checkpoint**: Use `/lean4:checkpoint` for verified save points
- **Review**: Use `/lean4:review` for quality audits

### Automation Tactics (Try in Order)

For simple proof steps, try these tactics in order:
1. `rfl` — definitional equality
2. `simp` — simplification
3. `ring` — ring equations
4. `linarith` — linear arithmetic
5. `nlinarith` — nonlinear arithmetic
6. `omega` — Presburger arithmetic
7. `exact?` — search mathlib for exact term
8. `apply?` — search mathlib for applicable lemma
9. `aesop` — automated proof search
10. `grind` — brute-force rewriting

### Quality Criteria

A proof is complete when:
- `lake build` passes
- Zero `sorry` in the agreed scope
- Only standard axioms used
- No statement changes without permission

## Architecture Notes

- This project is extracted from `DedekindDomain`
- **Current focus**: quadratic fields `Q(√d)` and ring-of-integers classification
- **Core.lean**: Contains `IsQuadraticParam`, `Qsqrtd`, nonsquare facts, and Exercise 2.4 formalization

### Module Dependencies

```
ClassificationOfIntegersOfQuadraticNumberFields.lean
    └── Core.lean
            ├── Base.lean
            ├── NonIso.lean
            ├── MinimalPolynomial.lean
            ├── HalfInt.lean
            ├── ModFourCriteria.lean
            └── ClassificationToZsqrtd.lean
```

## Common Tasks

### Adding a New Theorem

1. Add it to the appropriate module (e.g., `Core.lean` or a new focused module)
2. Follow project naming style (`snake_case`)
3. Add a docstring
4. Verify with `lake build`

### Searching mathlib

Before writing a new lemma, search mathlib:

```lean
-- Use Loogle: search by type signature
lean_loogle("?a → ?b → _")

-- Use LeanSearch: natural language
lean_leansearch("sum of two even numbers is even")

-- Use LeanFinder: goal-aware
lean_leanfinder("I have h : n < m and need n + 1 < m + 1")
```

### Troubleshooting

| Issue | Solution |
|-------|----------|
| Type mismatch | Use `lean_goal` to see actual vs expected type |
| Unknown identifier | Use `lean_leansearch` or `lean_loogle` |
| Slow compilation | Try `lean --nolsp` for faster checking |
| Instance not found | Check import order, try `haveI` to provide instance locally |

## Git Workflow

- Commit messages should describe mathematical or structural changes clearly
- Keep `.lake/` and build artifacts out of version control
- Ensure `lake build` succeeds before pushing

---

*Generated for AI agent consumption. Last updated: 2026-02-27*
