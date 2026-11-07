/-
Community DRAFT — NOT a verifier submission.

Trusted-statement + certificate-interface draft for the Big O Speedrun
"One-sample matroid prophet inequality" board
(https://bigospeedrun.com/other/matroid-prophet). Drafted as public input to
bigospeedrun/verifier#160, which the maintainers closed as not planned. Their
named blocker was scope, not the absence of a review repository: the Lean
evidence then public covered a scalar certificate only, and "the verifier
would have nothing to check against a trusted statement of the board's
theorem". This file states that theorem, parameterized by the scored
constant, so that a complete proof has a checkable target. The maintainers
own the route and any final statement; this file claims no authority over
either.

The board scores `C` in `E[R] >= C * E[OPT]`, higher is better: the
guaranteed fraction of the expected offline optimum for a one-sample online
selection rule on an arbitrary finite matroid, against a full-seed
"almighty" arrival-order adversary. Computation may take exponential time.

Model source (fetched 2026-11-06):
- OpenAI, openai/math @ 1581d4cbdd69a0faf34b2089614fe2a814316a6a (the commit
  proposed in #160; byte-identical to adc7f1241b42e322a6451854ab7e4b4c146bf78a,
  the commit the board cites), lean/ComparatorChallenges/MatroidProphet.lean.
  The `namespace OAI.MatroidProphet` block below is that file verbatim, with
  ONE omission: upstream's single deliberate `sorry` (`theorem one_sample`)
  is left out — this file carries the statement, not the proof. A frozen
  byte-exact copy lives in `upstream/MatroidProphet.lean`.

The scored quantity is exposed as `Ratios (c : ℝ)` — defeq to
`OneSampleChallenge` at the OpenAI baseline `((2:ℝ)^310)⁻¹` — plus a
`Bound (c : ℚ)` adapter in the exact form proposed in #160, a monotonicity
lemma, and per-row adapters. Design rationale and the certificate interface:
see DESIGN.md.

Build status is recorded in README.md (this draft: see the receipt there).
-/

import Mathlib

set_option autoImplicit false

/-! ## Upstream comparator statement (verbatim from openai/math @ 1581d4cb) -/

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace MatroidProphet

abbrev Weights (n : ℕ) := Fin n → ℝ
abbrev Seed (bits : ℕ) := Fin bits → Bool
abbrev ArrivalOrder (n : ℕ) := Equiv.Perm (Fin n)
instance arrivalOrderMeasurableSpace (n : ℕ) : MeasurableSpace (ArrivalOrder n) := ⊤

abbrev History (n : ℕ) (k : Fin n) := Fin (k.val + 1) → Fin n × ℝ

structure OnlineRule (n bits : ℕ) where
  decide : (k : Fin n) → Seed bits → Weights n → History n k → Bool
  measurable_decide : ∀ k, Measurable
    (fun x : Seed bits × (Weights n × History n k) => decide k x.1 x.2.1 x.2.2)

def prefixIndex {n : ℕ} (k : Fin n) (j : Fin (k.val + 1)) : Fin n :=
  ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt k.isLt)⟩

def history {n : ℕ} (v : Weights n) (π : ArrivalOrder n) (k : Fin n) : History n k :=
  fun j => let e := π (prefixIndex k j); (e, v e)

def decisionAt {n bits : ℕ} (A : OnlineRule n bits) (r : Seed bits)
    (s v : Weights n) (π : ArrivalOrder n) (k : Fin n) : Bool :=
  A.decide k r s (history v π k)

noncomputable def acceptedThrough {n bits : ℕ} (A : OnlineRule n bits) (r : Seed bits)
    (s v : Weights n) (π : ArrivalOrder n) (t : ℕ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun e =>
    (π.symm e).val < t ∧ decisionAt A r s v π (π.symm e) = true

noncomputable def accepted {n bits : ℕ} (A : OnlineRule n bits) (r : Seed bits)
    (s v : Weights n) (π : ArrivalOrder n) : Finset (Fin n) :=
  acceptedThrough A r s v π n

noncomputable def reward {n bits : ℕ} (A : OnlineRule n bits) (r : Seed bits)
    (s v : Weights n) (π : ArrivalOrder n) : ℝ :=
  ∑ e ∈ accepted A r s v π, v e

noncomputable def optimum {n : ℕ} (M : Matroid (Fin n)) (v : Weights n) : ℝ := by
  classical
  exact Finset.univ.sup' Finset.univ_nonempty
    (fun I : Finset (Fin n) => if M.Indep (I : Set (Fin n)) then ∑ e ∈ I, v e else 0)

def Feasible {n bits : ℕ} (M : Matroid (Fin n)) (A : OnlineRule n bits) : Prop :=
  ∀ (r : Seed bits) (s v : Weights n) (π : ArrivalOrder n) (t : ℕ),
    (∀ e, 0 ≤ s e) → (∀ e, 0 ≤ v e) →
    M.Indep (acceptedThrough A r s v π t : Set (Fin n))

def pairedCoordinates.{u} {n : ℕ} {Ω : Type u} (S V : Ω → Weights n)
    (i : Fin n × Bool) : Ω → ℝ :=
  if i.2 then fun ω => S ω i.1 else fun ω => V ω i.1

def OneSampleChallenge.{u} : Prop :=
  ∀ (n : ℕ) (M : Matroid (Fin n)), M.E = Set.univ →
    ∃ (bits : ℕ) (ν : Measure (Seed bits)), IsProbabilityMeasure ν ∧
    ∃ (A : OnlineRule n bits), Feasible M A ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (S V : Ω → Weights n) (R : Ω → Seed bits),
        Measurable S → Measurable V → Measurable R →
        (∀ᵐ ω ∂μ, ∀ e, 0 ≤ S ω e) →
        (∀ᵐ ω ∂μ, ∀ e, 0 ≤ V ω e) →
        iIndepFun (pairedCoordinates S V) μ →
        (∀ e, Measure.map (fun ω => S ω e) μ = Measure.map (fun ω => V ω e) μ) →
        IndepFun (fun ω => (S ω, V ω)) R μ →
        Measure.map R μ = ν →
        Integrable (fun ω => optimum M (V ω)) μ →
        ∀ (π : Ω → ArrivalOrder n), Measurable π →
          Integrable (fun ω => reward A (R ω) (S ω) (V ω) (π ω)) μ ∧
          ((2 : ℝ) ^ 310)⁻¹ * (∫ ω, optimum M (V ω) ∂μ) ≤
            ∫ ω, reward A (R ω) (S ω) (V ω) (π ω) ∂μ

end MatroidProphet

end OAI

/-! ## The board's scored constant, parameterized -/

namespace BigOSpeedrun.MatroidProphet

open MeasureTheory ProbabilityTheory
open scoped BigOperators

open OAI.MatroidProphet

noncomputable section

/-- The board's theorem with the coefficient exposed. `Ratios c` says: for
every full matroid on `n` labeled elements there is a measurable, feasible
online rule, simulated from a single sample per element by finitely many
seed bits, whose expected reward is at least `c` times the expected offline
optimum — against an arrival permutation that may depend on all samples,
values and seed bits (the "almighty full-seed adversary"). Larger `c` is
stronger. `Ratios ((2:ℝ)^310)⁻¹` is definitionally upstream
`OAI.MatroidProphet.OneSampleChallenge`. -/
def Ratios.{u} (c : ℝ) : Prop :=
  ∀ (n : ℕ) (M : Matroid (Fin n)), M.E = Set.univ →
    ∃ (bits : ℕ) (ν : Measure (Seed bits)), IsProbabilityMeasure ν ∧
    ∃ (A : OnlineRule n bits), Feasible M A ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (S V : Ω → Weights n) (R : Ω → Seed bits),
        Measurable S → Measurable V → Measurable R →
        (∀ᵐ ω ∂μ, ∀ e, 0 ≤ S ω e) →
        (∀ᵐ ω ∂μ, ∀ e, 0 ≤ V ω e) →
        iIndepFun (pairedCoordinates S V) μ →
        (∀ e, Measure.map (fun ω => S ω e) μ = Measure.map (fun ω => V ω e) μ) →
        IndepFun (fun ω => (S ω, V ω)) R μ →
        Measure.map R μ = ν →
        Integrable (fun ω => optimum M (V ω)) μ →
        ∀ (π : Ω → ArrivalOrder n), Measurable π →
          Integrable (fun ω => reward A (R ω) (S ω) (V ω) (π ω)) μ ∧
          c * (∫ ω, optimum M (V ω) ∂μ) ≤
            ∫ ω, reward A (R ω) (S ω) (V ω) (π ω) ∂μ

/-- The parameterization is definitional, not an interpretation. -/
theorem oneSampleChallenge_eq.{u} :
    OAI.MatroidProphet.OneSampleChallenge.{u} ↔ Ratios.{u} (((2 : ℝ) ^ 310))⁻¹ :=
  Iff.rfl

/-- Monotonicity: a proof at a larger constant certifies every smaller
nonnegative constant. This is what lets one framework proof, re-evaluated at
different exact analysis constants, serve the different board rows. -/
theorem ratios_mono.{u} {c c' : ℝ} (h0 : 0 ≤ c') (hle : c' ≤ c)
    (h : Ratios.{u} c) : Ratios.{u} c' := by
  intro n M hM
  obtain ⟨bits, ν, hν, A, hA, hAll⟩ := h n M hM
  refine ⟨bits, ν, hν, A, hA, ?_⟩
  intro Ω hΩ μ hμ S V R hS hV hR hnnS hnnV hInd hMarg hSeed hLaw hint π hπ
  obtain ⟨hint2, hineq⟩ :=
    hAll (Ω := Ω) μ S V R hS hV hR hnnS hnnV hInd hMarg hSeed hLaw hint π hπ
  refine ⟨hint2, ?_⟩
  have hopt : (0 : ℝ) ≤ ∫ ω, optimum M (V ω) ∂μ :=
    integral_nonneg fun ω => by
      rw [optimum]
      classical
      have h0 : (0 : ℝ) ≤ (fun I : Finset (Fin n) =>
          if M.Indep (I : Set (Fin n)) then ∑ e ∈ I, V ω e else 0)
          (∅ : Finset (Fin n)) := by
        show (0 : ℝ) ≤ (if M.Indep ((∅ : Finset (Fin n)) : Set (Fin n)) then
            ∑ e ∈ (∅ : Finset (Fin n)), V ω e else 0)
        split <;> simp [Finset.sum_empty]
      exact Finset.le_sup'_of_le (s := Finset.univ)
        (f := fun I : Finset (Fin n) =>
          if M.Indep (I : Set (Fin n)) then ∑ e ∈ I, V ω e else 0)
        (a := (0 : ℝ)) (b := (∅ : Finset (Fin n))) (Finset.mem_univ _) h0
  calc c' * (∫ ω, optimum M (V ω) ∂μ)
      ≤ c * (∫ ω, optimum M (V ω) ∂μ) := by nlinarith
    _ ≤ ∫ ω, reward A (R ω) (S ω) (V ω) (π ω) ∂μ := hineq

end

/-! ## Adapter layer

Each adapter shows how a row's mathematics enters the board target. The
hypothesis stands for the row's own proof transported to `Ratios` (a real
submission would import or replay the row's certificate and close the
hypothesis). Constants below are the exact values printed on the board
(2026-11-06 fetch). -/

section Adapters

/-- The form proposed in #160 for the controller to substitute:
`Race.bound : Bound (5114935688794994675 / 10 ^ 28)` etc. `Bound` fixes the
probability-space universe at `Type 0` (`Ratios` itself stays universe
polymorphic like upstream); whether the verifier's gate wants `ℚ` or `ℝ` is
#160 open question 1, a maintainer call. -/
def Bound (c : ℚ) : Prop := Ratios.{0} (c : ℝ)

/-- Rank 11 row (Agent breakthrough, OpenAI, 2026-10-06): the upstream
theorem itself, `C = 2⁻³¹⁰`. Upstream `OAI.MatroidProphet.one_sample` proves
this at exactly one deliberate `sorry`; a complete public Lean proof of it is
what the #160 decline named as the route precondition. -/
theorem openAIRow.{u} (h : OAI.MatroidProphet.OneSampleChallenge.{u}) :
    Ratios.{u} (((2 : ℝ) ^ 310))⁻¹ := h

/-- Rank 10 row (Claimed, bottlebrushes, 2026-10-10, `C = 2⁻³⁸`): a finer
exit certificate and a halved density loss applied to OpenAI's Lean
formalization (bottlebrushes/math @ b20ff915). -/
theorem bottlebrushesRow.{u} (h : Ratios.{u} (((2 : ℝ) ^ 38))⁻¹) :
    Ratios.{u} (((2 : ℝ) ^ 38))⁻¹ := h

/-- Rank 3 row (Claimed, Qiuyu Chen (Euler), 2026-10-19): OpenAI's
construction with Shea's refinements and the evaluation `B > 141` replaced
by the exact `B`; exact value 165971304277649481670619 / 324956758716416046811841770291200
(canghaimeng/openai-math-improvement @ b3c7abea). -/
noncomputable def ChenEulerC : ℝ := 165971304277649481670619 / 324956758716416046811841770291200

theorem chenEulerRow.{u} (h : Ratios.{u} ChenEulerC) : Ratios.{u} ChenEulerC := h

/-- Rank 4 row (Claimed, Ryan Shea, 2026-10-11): three-state generator
encoding and restricted overlap, exact value
4084754449786906742230661 / 8009094702029267287249256448000000
(shea256/matroid-prophet-inequality @ 8bafc1fd). -/
noncomputable def SheaC4 : ℝ := 4084754449786906742230661 / 8009094702029267287249256448000000

theorem sheaRow4.{u} (h : Ratios.{u} SheaC4) : Ratios.{u} SheaC4 := h

/-- Rank 5 row (Claimed, Ryan Shea, 2026-10-10): exact value
8003458533570087953 / 16807475946150704657203200000
(shea256/matroid-prophet-inequality @ deb20b28). -/
noncomputable def SheaC5 : ℝ := 8003458533570087953 / 16807475946150704657203200000

theorem sheaRow5.{u} (h : Ratios.{u} SheaC5) : Ratios.{u} SheaC5 := h

/-- Rank 6 row (Claimed, Ryan Shea, 2026-10-10): retained bases and
projected residuals, exact value
548933908320757 / 1325382348737372749824000
(shea256/matroid-prophet-inequality @ 8ba515ab). -/
noncomputable def SheaC6 : ℝ := 548933908320757 / 1325382348737372749824000

theorem sheaRow6.{u} (h : Ratios.{u} SheaC6) : Ratios.{u} SheaC6 := h

/-- Rank 7 row (Claimed, Ryan Shea, 2026-10-09): rank-charged residual
entropy, exact value 773895463001 / 3203794364409053184000
(shea256/matroid-prophet-inequality @ ff4187f0). -/
noncomputable def SheaC7 : ℝ := 773895463001 / 3203794364409053184000

theorem sheaRow7.{u} (h : Ratios.{u} SheaC7) : Ratios.{u} SheaC7 := h

/-- Rank 8 row (Claimed, Ryan Shea, 2026-10-09): joint residual encoding,
exact value 14995972860899 / 244123247301151948800000
(shea256/matroid-prophet-inequality @ 6e418031). -/
noncomputable def SheaC8 : ℝ := 14995972860899 / 244123247301151948800000

theorem sheaRow8.{u} (h : Ratios.{u} SheaC8) : Ratios.{u} SheaC8 := h

/-- Rank 9 row (Claimed, Ryan Shea, 2026-10-09): quadratic hazard potential,
exact value 9652683394380719 / 637507023635152349901619200
(shea256/matroid-prophet-inequality @ 7cffa2a7). -/
noncomputable def SheaC9 : ℝ := 9652683394380719 / 637507023635152349901619200

theorem sheaRow9.{u} (h : Ratios.{u} SheaC9) : Ratios.{u} SheaC9 := h

/-! Ranks 1–2 rows (Claimed, MultiAgency swarm, 2026-11-01/02): the board
states `C >= 5.114935688794994675e-10` and `C >= 5.110608508730856554e-10`,
with the exact fractions (1,265/1,274-digit) in
darkhipo/matroid-prophet-tight-corner @ 352d725 (exact_fraction.txt) and
darkhipo/matroid-prophet-exact-B @ dca1eb6. The adapter takes the exact
constant `c` at that level of precision and closes the stated threshold via
`ratios_mono` — the threshold rational is what #160 proposed substituting
into `Race.bound`. -/

noncomputable def SwarmBound1 : ℝ := 5114935688794994675 / (10 : ℝ) ^ 28

noncomputable def SwarmBound2 : ℝ := 5110608508730856554 / (10 : ℝ) ^ 28

theorem SwarmBound1_nonneg : (0 : ℝ) ≤ SwarmBound1 := by
  unfold SwarmBound1; norm_num

theorem SwarmBound2_nonneg : (0 : ℝ) ≤ SwarmBound2 := by
  unfold SwarmBound2; norm_num

theorem swarmRow1.{u} {c : ℝ} (hc : SwarmBound1 ≤ c) (h : Ratios.{u} c) :
    Ratios.{u} SwarmBound1 := ratios_mono SwarmBound1_nonneg hc h

theorem swarmRow2.{u} {c : ℝ} (hc : SwarmBound2 ≤ c) (h : Ratios.{u} c) :
    Ratios.{u} SwarmBound2 := ratios_mono SwarmBound2_nonneg hc h

/-! Controller-substituted entry-point shape, mirroring #160's proposal and
the board receipts (e.g. "The verifier checked Race.bound : ..."):

```lean
namespace Race
theorem bound : BigOSpeedrun.MatroidProphet.Bound (5114935688794994675 / 10 ^ 28) :=
  BigOSpeedrun.MatroidProphet.swarmRow1 <exact constant, monotone> <row certificate, imported>
end Race
```
-/

end Adapters

end BigOSpeedrun.MatroidProphet
