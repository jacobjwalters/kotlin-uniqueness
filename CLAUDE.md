= Kotlin Uniqueness Types Formalization

Formalization of a uniqueness type system for Kotlin in Lean 4,
with an informal specification in Typst.

== Structure

- `doc/` — Typst informal specification (Lbase, Lclass)
- `lean-formalisation/` — Lean 4 formalization
  - `LeanFormalisation/LBase.lean` — main Lbase system
  - `LeanFormalisation/LBaseHelpers.lean` — helper lemmas
  - `LeanFormalisation/LCoreSim.lean` — CPS compilation to LCore (in progress)
  - `LeanFormalisation/Defs.lean` — earlier attempt (superseded by LBase.lean)

== Git workflow

- When work reaches a reviewable state (compiles, tests pass), create a PR
  on a descriptive branch rather than just committing. Don't wait to be asked.
- PRs should target `main`.

== Guidance for using Lean

- You have access to the Lean MCP server, and should feel free to use it.
- You may use all of Mathlib.
  - If you would like to use other libraries, ask first.
- You may use `sorry` liberally, but we will want to eliminate them eventually.
  - Mark them with a comment on why they're left open for now.
- Make sure the build output is clean:
  - Remove `#check` and `#eval` when you're done with a part.
  - Make sure to fix linter warnings.
- Helper theorems should be marked as lemmas.
- Keep BEST-PRACTICES.md updated when you spot things that should
  be taken into account in the future.
