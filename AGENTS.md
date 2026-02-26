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
lake exe cache get
lake build
lake clean
lean ClassificationOfIntegersOfQuadraticNumberFields/Core.lean
```

### Running Tests

Lean 4 proofs are verified during compilation.

```bash
# Verify the full project
lake build

# Verify a single file
lean ClassificationOfIntegersOfQuadraticNumberFields/Core.lean
```

### LSP Tools (Recommended for AI Agents)

Use Lean LSP tools before and after edits:

- `lean_diagnostic_messages`
- `lean_goal`
- `lean_hover_info`
- `lean_loogle`
- `lean_state_search`
- `lean_leansearch`

### Running CI Locally

```bash
lake build
```

## Code Style Guidelines

### File Organization

- Main entry point: `ClassificationOfIntegersOfQuadraticNumberFields.lean`
- Core formalization file: `ClassificationOfIntegersOfQuadraticNumberFields/Core.lean`
- Use `namespace ClassificationOfIntegersOfQuadraticNumberFields` for project declarations
- Group related content with `section`/`namespace`, and close with explicit `end`

### Naming Conventions

- **Files**: CamelCase
- **Definitions/Theorems/Lemmas**: `snake_case`
- **Variables**: lowercase (`d`, `d₁`, `d₂`, `x`)
- **Type variables**: capitals (`R`, `K`)
- Prefer Unicode mathematical symbols (`→`, `∀`, `∃`, `↔`, `∈`, `≠`)

### Import Style

```lean
import Mathlib
import ClassificationOfIntegersOfQuadraticNumberFields.Core
```

- Put `Mathlib` first
- Then local imports in dependency order
- Avoid unused imports

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

### Documentation

- Add docstrings (`/-- ... -/`) for new defs/theorems
- Keep module-level motivation in `/-! ... -/` blocks where useful

### Error Handling / Proof Completeness

- Temporary `sorry` is allowed during development
- Do not leave `sorry` in final deliverables unless explicitly requested

### Lean Options (from `lakefile.toml`)

- `pp.unicode.fun = true`
- `relaxedAutoImplicit = false`
- `weak.linter.mathlibStandardSet = true`
- `maxSynthPendingDepth = 3`

## Architecture Notes

- This project is extracted from `DedekindDomain`
- Current focus: quadratic fields `Q(√d)` and ring-of-integers classification prerequisites
- `Core.lean` contains `IsQuadraticParam`, `Qsqrtd`, nonsquare facts, and Exercise 2.4 first-part formalization

## Common Tasks

### Adding a New Theorem

1. Add it to `ClassificationOfIntegersOfQuadraticNumberFields/Core.lean` (or a new focused module)
2. Follow project naming style (`snake_case`)
3. Add a docstring
4. Verify with `lake build`

## Git Workflow

- Commit messages should describe mathematical or structural changes clearly
- Keep `.lake/` and build artifacts out of version control
- Ensure `lake build` succeeds before pushing

---

*Generated for AI agent consumption. Last updated: 2026-02-26*
