# zfolean4

`zfolean4` is an AI-assisted Lean 4 port of a deep embedding of first-order set theory. It provides
syntax with de Bruijn indices, lifting and substitution operations, and an intuitionistic
natural-deduction proof calculus with equality.

The library contains:

- `Zfolean4.Fol`: first-order terms, formulas, substitutions, and proof terms.
- `Zfolean4.Zfc`: the ZFC language and axioms, including a formal proof that `ω` is the
  smallest inductive set.
- `Zfolean4.Izf`: an IZF presentation with primitive set-forming operations and the
  corresponding theorem about `ω`.
- `Zfolean4.Tls`: the `tls` tactic, which hides routine de Bruijn-index and transformed-context
  bookkeeping inside object-theory proofs.

The project uses Lean 4 and Mathlib `v4.33.0-rc2`. Build it from the project directory with:

```sh
lake build
```
