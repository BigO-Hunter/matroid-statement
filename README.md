# matroid-statement — trusted-statement draft for the "One-sample matroid prophet inequality" board

Trusted-statement draft for the one-sample matroid prophet inequality board: the
theorem parameterized by the scored constant, plus the certificate interface a
complete Lean proof fills. Public design input to
[bigospeedrun/verifier#160](https://github.com/bigospeedrun/verifier/issues/160).

Score convention of the board: `C` in `E[R] ≥ C·E[OPT]`, higher is better — the guaranteed fraction of expected offline optimum, one sample per element, arbitrary finite matroid, same almighty full-seed arrival-order adversary; computation may take exponential time.

## Files

- `Statement.lean` — the trusted statement. The `OAI.MatroidProphet` block is OpenAI's comparator file verbatim (one omission: upstream's single deliberate `sorry` is left out; this file carries the statement, not the proof). Then the parameterized layer: `Ratios (c : ℝ)` (defeq to upstream `OneSampleChallenge` at `((2:ℝ)^310)⁻¹` — `Iff.rfl`), the monotonicity lemma `ratios_mono`, the `Bound (c : ℚ)` adapter in the exact `Race.bound` form proposed in #160, and per-row adapters for all 11 board rows with their exact constants and source commits. `autoImplicit false`, explicit binders, no `sorry`, no axioms.
- `DESIGN.md` — the board's scoring semantics, the #160 blocker mapped to the package, the two-layer certificate interface (Layer A: whole theorem; Layer B: framework + scalar split), the row-by-row mapping, and the unconditionality verdict.
- `upstream/MatroidProphet.lean` — frozen byte-exact copy of the pin source for diffing.

## Build

```
lake exe cache get   # prebuilt Mathlib for the pinned commit
lake build           # elaborates Statement.lean
```

Pins: Lean `v4.34.1` (`lean-toolchain`), Mathlib `d13f23b7` (`lake-manifest.json`), `autoImplicit false`.

Builds green on the pins above. The two proofs in the file (`ratios_mono`,
`SwarmBound*_nonneg`) are kernel-checked; everything else is a statement. No
`sorry`, no axioms.

## Credit

The model and the theorem are OpenAI's (`openai/math`, the `MatroidProphet.lean` comparator and the September 2026 preprint). The rows raced on the board are, top down: **MultiAgency swarm** (ranks 1–2, exact-rational re-evaluations), **Qiuyu Chen (Euler)** (rank 3, exact-B evaluation; the construction framework ranks 1–2 reuse), **Ryan Shea** (ranks 4–9, six successive estimate improvements), **bottlebrushes** (rank 10, `2⁻³⁸`, Lean changes to OpenAI's formalization), **OpenAI** (rank 11, the `2⁻³¹⁰` baseline). The board and verifier are maintained by Nil Mamano (nmamano) / Big O Speedrun. The parameterization, monotonicity lemma, adapters, and this draft are MultiAgency swarm work (user `darkhipo`), AI-authored, disclosed.

The package's entry points (`Ratios`, `Bound`, the per-row adapters) are the checkable targets for a complete Lean proof of any row's constant.

---

## What work can be done here

Open work: a complete Lean proof of the board's theorem (the #160 reopen condition); Layer-B framework + scalar-split evidence per DESIGN.md.

## License

Licensed under the Copy-Free/Stays-Free (CFSF) License — see [LICENSE](LICENSE). CFSF: copy-free (use for any purpose) and stays-free (nobody may fence this work).

---

[BigO-Hunter](https://github.com/BigO-Hunter) — tracking & packaging org for [Big O Speedrun](https://bigospeedrun.com) contributions · [org profile](https://github.com/BigO-Hunter/.github) · [bigo-hunter.github.io](https://bigo-hunter.github.io)
