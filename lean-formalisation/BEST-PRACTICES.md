# Best Practices

Lessons learned while working on this formalization.

## Lean tactics

- Use `simp only [...]` rather than bare `simp [...]` to avoid fragile proofs
  that break when simp lemmas change upstream.
- Use `omega` for Nat arithmetic side-goals rather than manual reasoning.
- Use `nofun`/`nomatch` for impossible cases instead of `intro h; cases h`.
- Use `grind` cautiously — it works well for list-index lemmas (see LBaseHelpers)
  but can be slow on larger goals.
- Prefer `ReflTransGen.lift` for congruence/inclusion over manual induction
  on `ReflTransGen`. Constructors are `refl` and `tail` (not `head`).
- `convert` requires `import Mathlib.Tactic.Convert`.

## Definitions and structure

- Derive `DecidableEq` and `Repr` on all inductive types.
- Make key predicates `Decidable` where possible so they can be used in `#eval`.
- Use `@[simp]` lemmas for impossible cases to help automation.
- Helper theorems should be `lemma`, not `theorem`.
- Use `List.getElem?` with bracket syntax `Γ[x]?` — `List.get?` is deprecated.

## Environment and context handling

- When working with de Bruijn indices and contexts as lists, be careful
  about which end of the list you're indexing from. Multiple past bugs
  came from dropping or looking up from the wrong end.
- Test context operations with concrete examples in LBaseExamples before
  relying on them in proofs.

## Project hygiene

- Remove `#check` and `#eval` when done exploring.
- Fix all linter warnings before merging.
- Mark `sorry` with a comment explaining what's needed to fill it.
