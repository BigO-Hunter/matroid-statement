# DESIGN.md — the matroid-prophet trusted statement and certificate interface

Community DRAFT, 2026-11-06. Public input to bigospeedrun/verifier#160 (closed as not
planned). Not a submission; claims no authority over the route or any final statement.

## 0. What the board scores (read from the live page, 2026-11-06)

The [board](https://bigospeedrun.com/other/matroid-prophet) races the constant `C` in

    E[R] ≥ C · E[OPT]        (higher is better)

— the **one-sample matroid prophet inequality**: an arbitrary finite matroid; the
online player sees exactly **one sample per element** (sample and true value i.i.d.
per coordinate, sample independent of the adversary's randomness); a **"same
almighty full-seed arrival-order adversary"** chooses the arrival permutation with
full knowledge of all samples, all values, and the player's seed; decisions are
irrevocable and prefixes must stay matroid-independent; `R` is the selected reward,
`OPT` the offline optimum. Computation may take exponential time — the race is over
the guaranteed **fraction**, not runtime. OpenAI's preprint *"One-Sample Suffices
for Matroid Prophet Inequalities against an Almighty Adversary"* (2026-09-23)
opened the race at `C = 2⁻³¹⁰` (the Agent-breakthrough row). Rows are ranked by
descending bound; `2⁻³¹⁰ ≈ 8.3·10⁻⁹⁴`, so the race is 10+ orders of magnitude deep
in exact rational arithmetic. Evidence levels: all 11 rows live are **Claimed**
(published, unchecked); none is Lean Verified. ("12 rows" appears in older notes;
the live page shows 11 — rank list below.)

## 1. Why this package exists — the #160 blocker, stated precisely

The #160 decline did **not** decline for absence of a review repository — verbatim:

> "The board has no review repository, so that is not the reason. The reason is the
> scope boundary you state: the Lean check covers the scalar certificate, and the
> universal matroid theorem (fixed-vector rule, exposure and hybrids, measurability,
> one-sample simulation) is not proved. The verifier would have nothing to check
> against a trusted statement of the board's theorem, so your seven questions about
> the statement form, pins and limits do not arise yet."
>
> "When a complete Lean proof of the board's statement is public, you can open a new
> ask-first issue."

So the route precondition is a **complete Lean proof of the board's theorem**. What
that means is exactly what was undefined — the trusted statement is the definition.
This package freezes the board's theorem as a Lean proposition (pinned upstream byte
for byte, per route-policy §3), exposes the scored constant as a parameter, and
enumerates the obligations a row must discharge to make a proof "complete" against
it.

## 2. Statement shape (Statement.lean)

- `namespace OAI.MatroidProphet` — upstream `MatroidProphet.lean` **verbatim**
  (openai/math @ `1581d4cb`, byte-identical to the board-cited `adc7f124`), one
  omission: upstream's single deliberate `sorry` (`theorem one_sample`) is left out;
  a byte-exact frozen copy sits in `upstream/MatroidProphet.lean` for diffing.
- `BigOSpeedrun.MatroidProphet.Ratios (c : ℝ)` — the identical challenge with the
  coefficient exposed; `OneSampleChallenge.{u} ↔ Ratios.{u} ((2:ℝ)^310)⁻¹` is
  `Iff.rfl` (definitional, no interpretation).
- `ratios_mono` — a proof at constant `c` certifies every `0 ≤ c' ≤ c`. This is what
  lets one framework proof serve every row: rows differ only in the exact analysis
  constant their mathematics evaluates.
- `Bound (c : ℚ)` — the exact `Race.bound : Bound (5114935688794994675 / 10 ^ 28)`
  form proposed in #160.
- Per-row adapters naming every row's exact constant and source commit, so a row's
  certificate has a named entry point. `autoImplicit false`; explicit binders.

## 3. The certificate interface — what a Lean-Verified row needs

The board's theorem is one universal statement; a row is that statement at a larger
constant. Complete = sorry-free proof of `Ratios c_row` (equivalently `Bound c_row`
through the cast). Two honest decompositions:

**Layer A — the whole theorem at once.** Sorry-free `Ratios c_row`. Everything
below is inside one proof. This is the target the route policy gates on
("complete Lean proof of the board's statement is public").

**Layer B — framework + scalar split** (the honest decomposition of the #160 scope
boundary). A public Lean development proving the *constant-independent* machinery:

1. **Fixed-vector rule** — from the one-sample distribution, construct the online
   rule (a fixed seed `bits`, a fixed measure `ν`) and prove `Feasible M A` for all
   matroids (`acceptedThrough` stays inside `M`'s independent sets).
2. **Exposure and hybrids** — the probabilistic skeleton: move from the joint
   `(sample, value)` law to the hybrid/exposure couplings that make the almighty
   adversary's information advantage quantitative; prove the master inequality
   `E[reward] ≥ κ(c') · E[OPT]` with the analysis constant `c'` left symbolic.
3. **Measurability** — every `measurable_decide`, `Measure.map`, `iIndepFun` and
   integrability side condition (already partially encoded upstream).
4. **One-sample simulation** — `Measure.map R μ = ν`: the rule's randomness is
   exactly the finitely many seed bits.

Layer B ends in an interface lemma of the shape
`framework : (h : ScalarCert c') → Ratios c'`, leaving only

5. **ScalarCert c'** — the exact-rational arithmetic over the construction's
   finitely many conditions (the 28-condition checker of our rank-1 row is this
   artifact outside Lean; a Lean version is `decide`/`norm_num`-sharded, see the
   #157 resource lesson: shard kernel monoliths, don't `decide +kernel` them whole).

Each row plugs in as: Layer B (shared, prove once) + its own `ScalarCert` at its
exact constant. A row whose mathematics changes the *construction* (OpenAI's does
both; Shea's rows change estimates of OpenAI's construction; Chen's row and ours
re-evaluate constants) states its delta against the same framework.

## 4. Row-by-row mapping (constants as on the live board, 2026-11-06)

| Rank | Author | Constant | Layer B delta needed |
|---|---|---|---|
| 1 | MultiAgency swarm (darkhipo/matroid-prophet-tight-corner @ 352d725) | ≥ 5.114935688794994675e-10 (exact fraction, 1,265/1,274 digits, exact_fraction.txt) | construction = Chen's; re-optimized three analysis constants → ScalarCert |
| 2 | MultiAgency swarm (darkhipo/matroid-prophet-exact-B @ dca1eb6) | ≥ 5.110608508730856554e-10 | exact-B evaluation of Chen's C(B) → ScalarCert |
| 3 | Qiuyu Chen (Euler) (canghaimeng/openai-math-improvement @ b3c7abea) | 165971304277649481670619/324956758716416046811841770291200 | OpenAI construction + Shea refinements, exact B → ScalarCert; the underlying paper (PDF, no independent check) is the frame for rows 1–2 |
| 4–9 | Ryan Shea (shea256/matroid-prophet-inequality @ 8bafc1fd, deb20b28, 8ba515ab, ff4187f0, 6e418031, 7cffa2a7) | exact fractions, ≈5.10e-10 down to ≈1.51e-11 | improved estimates of OpenAI's construction (three-state generator, restricted overlap, retained bases, rank-charged residuals, joint residual encoding, quadratic hazard) → six ScalarCerts on a shared frame |
| 10 | bottlebrushes (bottlebrushes/math @ b20ff915) | 2⁻³⁸ | Lean *changes to OpenAI's formalization* (finer exit certificate, halved density loss) — the only row already partially in Lean; board notes it was inspected, not built |
| 11 | OpenAI (openai/math @ adc7f124) | 2⁻³¹⁰ | the upstream theorem: construction AND framework in one development, closed by exactly one deliberate `sorry` |

## 5. Unconditionality verdict

**All 11 rows are unconditional.** Every row keeps OpenAI's construction (or a
refinement of it) and improves the *analysis*; none invokes a conjecture — no
unproven prophet-inequality or matroid-secretary conjecture appears in any row's
stated chain, and the OpenAI baseline theorem itself is a completed (written,
sorry-in-Lean-only) proof. The general literature backdrop (one-sample prophet /
matroid-secretary line, e.g. Correa–Saenz–Singla et al.) is likewise a body of
unconditional theorems; the board's almighty-adversary variant is OpenAI's own
model and does not depend on it. So **no conditional-row variant of this package is
needed**: the honest caveat is not conjecture-dependence but *verification
absence* — every row above rank 11 is a written proof, and for rank 3 the proof is
a PDF no third party has checked.

## 6. What this package is not

- Not a route request; #160 asked the questions and maintainers answered. No new
  verifier issue opens until a complete Layer-A proof exists, per the decline's own
  instruction.
- Not a claim on the rows: all constructions and analyses are the row holders'
  (credit in README.md). The statement transcribes OpenAI's Lean model; the
  parameterization and adapters are ours.
- Not final: the maintainers own the route, the pins, and any final statement.

## 7. Unresolved / flagged honestly

- The build receipt for this draft is in README.md (Statement.lean compiles clean /
  does not yet compile — one line states which). The mono lemma is the only proof
  in the file; everything else is a statement.
- Whether OpenAI's *full* repository (beyond the comparator file) already proves
  part of Layer B was not established — the comparator file carries the single
  `sorry`, but the surrounding corpus was not audited for this draft.
- The controller-side `Race.bound` naming and the `ℚ`-vs-`ℝ` gate type are #160's
  open questions 1–2; they remain maintainer calls.
