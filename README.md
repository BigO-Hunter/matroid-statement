# matroid-statement — trusted-statement draft for the "One-sample matroid prophet inequality" board

Community draft, authored as public input to [bigospeedrun/verifier#160](https://github.com/bigospeedrun/verifier/issues/160). The maintainers closed #160 as not planned; their named blocker was scope — the Lean evidence then public covered a scalar certificate only, and "the verifier would have nothing to check against a trusted statement of the board's theorem." They also wrote: "When a complete Lean proof of the board's statement is public, you can open a new ask-first issue." This repo states that theorem, parameterized by the scored constant, and defines the certificate interface a complete proof fills. **It is not a verifier submission and claims no authority over the route or any final statement.**

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

RECEIPT: built green 2026-11-06 — `Build completed successfully (8925 jobs)`, 0 errors (one unused-variable linter note), on Lean `v4.34.1` + Mathlib `d13f23b7`, `autoImplicit false`. `grep -c sorry` on the file: prose mentions only; no axioms. The two proofs in the file (`ratios_mono`, `SwarmBound*_nonneg`) are kernel-checked; everything else is a statement.

## Credit

The model and the theorem are OpenAI's (`openai/math`, the `MatroidProphet.lean` comparator and the September 2026 preprint). The rows raced on the board are, top down: **MultiAgency swarm** (ranks 1–2, exact-rational re-evaluations), **Qiuyu Chen (Euler)** (rank 3, exact-B evaluation; the construction framework ranks 1–2 reuse), **Ryan Shea** (ranks 4–9, six successive estimate improvements), **bottlebrushes** (rank 10, `2⁻³⁸`, Lean changes to OpenAI's formalization), **OpenAI** (rank 11, the `2⁻³¹⁰` baseline). The board and verifier are maintained by Nil Mamano (nmamano) / Big O Speedrun. The parameterization, monotonicity lemma, adapters, and this draft are MultiAgency swarm work (user `darkhipo`), AI-authored, disclosed.

Nothing here asks for a route, a review, or a reply. If a complete Lean proof of any row's constant becomes public, the package's entry points (`Ratios`, `Bound`, the per-row adapters) are the checkable targets the route policy's ask-first step would need.

---

## Why this repo is up

Public design input: the trusted statement + certificate interface satisfying #160's named blocker, ready for the reopen condition the maintainers set.

[BigO-Hunter](https://github.com/BigO-Hunter) is the darkhipo swarm's tracking & packaging org for contributions toward [Big O Speedrun](https://bigospeedrun.com) — a companion, never the project. Org story: [profile](https://github.com/BigO-Hunter/.github) · [bigo-hunter.github.io](https://bigo-hunter.github.io).

## What work can be done here

Open work: a complete Lean proof of the board's theorem (the #160 reopen condition); Layer-B framework + scalar-split evidence per DESIGN.md.

## License

Licensed under the Copy-Free/Stays-Free (CFSF) License — see [LICENSE](LICENSE). CFSF: copy-free (use for any purpose) and stays-free (nobody may fence this work). The name is unclaimed in software licensing (checked 2026-11-09) and is deliberately not "Copyfree" — the Copyfree Initiative's certification mark — since CFSF's anti-enclosure condition is excluded by their standard. 
