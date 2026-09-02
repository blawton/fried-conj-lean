/-
BRIDGE COMPOSITION SKELETON (8/15 pm) — obligation 1-BRIDGE of note_preflight_8_15.md,
route (b): FK-conditioning / disintegration at the trace level.

Architecture (per Ben, 8/15 pm): the hypothesis is the kinetic gap AS POSED by HT/TZ
(sphere-bundle side); the SM→T*M bridge is OURS. Route (b) bridges the quantities the
T*M leg consumes (FK expectations / traces), not spectra: condition the fiber-OU process
on its radial path; the angular remainder is an SM-type process on the radial clock; the
posed SM gap bounds the CONDITIONAL expectation; the radial law is then averaged.

This file machine-checks the composition's logical spine — the steps that are pure
measure theory — with NO axioms: both theorems are fully proved from Mathlib.
The two analytic inputs of route (b) enter as HYPOTHESES (theorem-with-citations style):
  (SM-GAP)   ‖E[X | radial σ-algebra]‖ ≤ B pointwise a.e., B radial-measurable
             — to be supplied by the posed HT/TZ gap, run on the radial clock;
  (RAD-CONC) ∫ B dμ ≤ ε — the radial concentration / Laplace-transform lemma.

⚡MODEL-TEST SCOPE WARNING (s1_trace_bridge_composition_8_15.py, run 8/15 pm):
on S¹ the disintegration identity is EXACT (T1: transfer-matrix conditional estimator
== direct MC == closed form at every b), but the MODULUS route certified here is the
SMALL-b spine only: for 2πkb ≳ 1 the conditional modulus saturates (quenched exponent
E[−log‖E[X|𝒢]‖] → log 2 — the single initial coin flip) while the true decay
(annealed exponent, b-rigid rate 2π²k²) is carried by PHASE CANCELLATION of the
conditional expectations across radial paths — measure concentration in trace
integrals, the T*M family's native mechanism. The large-b regime therefore needs a
phase-aware version (v2): conditional polar decomposition X-side, oscillatory
concentration radial-side. Satisfiability of the hypothesis pair at nontrivial X is
witnessed numerically by the S¹ model in the mixing regime (quenched/annealed → 1 as
b → 0).

THEOREMS (zero sorries, zero axioms):
  towerModulus       — ‖E[X]‖ ≤ E[‖E[X|m]‖]: integral_condExp + norm_integral.
                       The tower step T1 validates numerically.
  modulusComposition — (SM-GAP) + (RAD-CONC) ⇒ ‖E[X]‖ ≤ ε.
  rateComposition    — the ε = C'·exp(−λt) instantiation: uniform decay of the T*M
                       FK expectation from a conditional gap at clock rate γ plus a
                       clock Laplace bound. The shape 1-BRIDGE feeds into the budget.
-/
import Mathlib

namespace FriedBridgeComposition

open MeasureTheory

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {m : MeasurableSpace Ω}

/-- Tower-modulus inequality: the disintegration step of route (b). `m` is the radial
σ-algebra; `μ[X|m]` is the SM-side conditional expectation on the radial clock. -/
theorem towerModulus (hm : m ≤ m₀) (X : Ω → ℂ) :
    ‖∫ ω, X ω ∂μ‖ ≤ ∫ ω, ‖(μ[X | m]) ω‖ ∂μ := by
  rw [← integral_condExp hm]
  exact norm_integral_le_integral_norm _

/-- Modulus composition: conditional gap bound (SM-GAP) + radial averaging (RAD-CONC)
⇒ decay of the full expectation. Small-b spine of 1-BRIDGE (see scope warning). -/
theorem modulusComposition (hm : m ≤ m₀) (X : Ω → ℂ) (B : Ω → ℝ)
    (hB : Integrable B μ)
    (hgap : ∀ᵐ ω ∂μ, ‖(μ[X | m]) ω‖ ≤ B ω)
    {ε : ℝ} (hconc : ∫ ω, B ω ∂μ ≤ ε) :
    ‖∫ ω, X ω ∂μ‖ ≤ ε :=
  le_trans (towerModulus μ hm X)
    (le_trans (integral_mono_ae integrable_condExp.norm hB hgap) hconc)

/-- Rate form: SM gap at clock rate γ on the radial clock τ, plus the clock's Laplace
bound, give uniform exponential decay — the statement shape the K10 budget consumes.
`C, γ` come from the posed HT/TZ gap (citation); the Laplace bound is the radial
concentration lemma 1-BRIDGE must prove for the fiber-OU radial process. -/
theorem rateComposition (hm : m ≤ m₀) (X : Ω → ℂ) (τ : Ω → ℝ)
    (C C' γ lam t : ℝ)
    (hint : Integrable (fun ω => C * Real.exp (-(γ * τ ω))) μ)
    (hgap : ∀ᵐ ω ∂μ, ‖(μ[X | m]) ω‖ ≤ C * Real.exp (-(γ * τ ω)))
    (hconc : ∫ ω, C * Real.exp (-(γ * τ ω)) ∂μ ≤ C' * Real.exp (-(lam * t))) :
    ‖∫ ω, X ω ∂μ‖ ≤ C' * Real.exp (-(lam * t)) :=
  modulusComposition μ hm X _ hint hgap hconc

end FriedBridgeComposition
