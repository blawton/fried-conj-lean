/-
BRIDGE TWO-CHANNEL SPINE (8/16) — Lean v2 for obligation 1-BRIDGE of
note_preflight_8_15.md; companion to bridge_composition_8_15.lean (v1, modulus channel)
and phase_lemma_model_tests_8_16.md (the model evidence that fixed these axiom shapes).

⚡THE SIMPLIFICATION (8/16, per Ben — "the answer is simpler than you think"): the two
channels are NOT a case split with a seam to match. Both bounds are simultaneously valid
inequalities at every parameter value, so the bridge bound composes by MIN of two
always-true bounds; the two-regime picture of the model tests is a DIAGNOSIS of which
mechanism produces the decay, never a proof-side case analysis. "Coverage" reduces to
the pointwise statement max(rate_mod, rate_phase) ≥ β > 0 — a fact about two functions,
not a patching argument. This file retires the former "seam/coverage" obligation.

CHANNELS (analytic inputs enter as cited hypotheses; zero axioms in this file):
  MODULUS channel = v1's modulusComposition/rateComposition
    (SM gap on the radial clock ∫γ_frozen ds — toy: conditional_vs_autonomous_toy_8_15).
  PHASE channel (this file): the conditional expectation is approximated by a COMPOSITE
    radial functional Y (on S¹: cos(θ·∫r_s ds) — phase = radial AREA functional, exact;
    phase_lemma_model_tests_8_16 Part A), whose oscillatory average decays by
    (AREA-SPREAD) — characteristic-function decay of the radially clocked additive
    functional (on S¹: the exact Gaussian closed form, valid at EVERY b, prefactor
    e^{cb²} absorbed by the budget per budget_davies_prefactor_check_8_15). The
    approximation remainder (flip corrections) is the mixing channel's object.
    ⚡Model-test design input: polar decoupling FAILS (ratio 0.92–1.28) — the hypothesis
    is stated on the composite, never as separate phase/modulus factors.

THEOREMS (zero sorries, zero axioms):
  phaseChannel      — plain split: ‖E X‖ ≤ E‖X − Y‖ + ‖E Y‖ ≤ ε₁ + ε₂.
  phaseChannelCond  — the conditional form: remainder measured against μ[X|m] (the flip
                      corrections live at the conditional level), via integral_condExp.
  twoChannelMax     — both channels hold ⇒ the min bound. The whole "seam": one line.

ITEM-(4) SPINES (added 8/18, per Ben — "the bridge file should have everything"; the
composition joints of the E[Y]-decay lemma, item4_composition_lab_8_17.md; analytic
inputs — FK eigenvalue identifications, LDP tilt/Airy bounds, per-class rates — remain
cited hypotheses):
  classwiseInterlock   — finite path-class partition: per-class bounds sum to a global
                         bound. The interlock lemma's structural content ("no path class
                         evades both channels" then reduces to per-class citations).
  airyWindowExponent   — rpow arithmetic: the Airy rate b^{−4/3} times the T = A·b^{10/3}
                         window is exactly A·b² — the exponent bookkeeping of the
                         three-power table.
  budgetWindow /
  item4Admissible      — the admissible-region arithmetic, machine-checked: with margin
                         βA > c, the b² decay beats the Davies prefactor e^{cb²} and any
                         polynomial loss K·log b past an EXPLICIT threshold
                         b₀ = max(1, K/(βA − c)). (The budget's "Lean-ready" claim, #6,
                         now literal.)
  sphericalFubini /
  directionalReduction — the Fubini swap behind "Y = spherical mean": cross-path average
                         of the spherical mean = direction-average of directional
                         characteristic functions, and its norm bound — the step that
                         reduces the flat case to the classical radial citation.
-/
import Mathlib

set_option linter.style.header false

namespace FriedBridgeTwoChannel

open MeasureTheory

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {m : MeasurableSpace Ω}

omit [IsProbabilityMeasure μ] in
/-- PHASE channel, plain form: split X into the composite radial functional Y plus a
remainder. (AREA-SPREAD) bounds ‖∫Y‖; the remainder integral is the mixing-channel
object (flip corrections). -/
theorem phaseChannel (X Y : Ω → ℂ)
    (hX : Integrable X μ) (hY : Integrable Y μ)
    {ε₁ ε₂ : ℝ}
    (hflip : ∫ ω, ‖X ω - Y ω‖ ∂μ ≤ ε₁)
    (hspread : ‖∫ ω, Y ω ∂μ‖ ≤ ε₂) :
    ‖∫ ω, X ω ∂μ‖ ≤ ε₁ + ε₂ := by
  have hsub : Integrable (fun ω => X ω - Y ω) μ := hX.sub hY
  calc ‖∫ ω, X ω ∂μ‖
      = ‖(∫ ω, (X ω - Y ω) ∂μ) + ∫ ω, Y ω ∂μ‖ := by
        rw [integral_sub hX hY]; ring_nf
    _ ≤ ‖∫ ω, (X ω - Y ω) ∂μ‖ + ‖∫ ω, Y ω ∂μ‖ := norm_add_le _ _
    _ ≤ (∫ ω, ‖X ω - Y ω‖ ∂μ) + ‖∫ ω, Y ω ∂μ‖ := by
        gcongr; exact norm_integral_le_integral_norm _
    _ ≤ ε₁ + ε₂ := add_le_add hflip hspread

/-- PHASE channel, conditional form: the flip-correction remainder is naturally measured
at the conditional level, ‖μ[X|m] − Y‖ ≤ B pointwise with ∫B ≤ ε₁ (B and Y radial
functionals). Uses the tower step, then splits around the composite. -/
theorem phaseChannelCond (hm : m ≤ m₀) (X Y : Ω → ℂ) (B : Ω → ℝ)
    (hY : Integrable Y μ) (hB : Integrable B μ)
    {ε₁ ε₂ : ℝ}
    (hflip : ∀ᵐ ω ∂μ, ‖(μ[X | m]) ω - Y ω‖ ≤ B ω)
    (hB1 : ∫ ω, B ω ∂μ ≤ ε₁)
    (hspread : ‖∫ ω, Y ω ∂μ‖ ≤ ε₂) :
    ‖∫ ω, X ω ∂μ‖ ≤ ε₁ + ε₂ := by
  rw [← integral_condExp hm]
  refine phaseChannel μ _ Y integrable_condExp hY ?_ hspread
  calc ∫ ω, ‖(μ[X | m]) ω - Y ω‖ ∂μ
      ≤ ∫ ω, B ω ∂μ := integral_mono_ae (integrable_condExp.sub hY).norm hB hflip
    _ ≤ ε₁ := hB1

omit [IsProbabilityMeasure μ] in
/-- TWO-CHANNEL MAX: both channel bounds are always-valid inequalities, so the bridge
bound is their min — the entire former "seam/coverage obligation" is this one line.
Uniform positivity of the better rate is a pointwise fact about two rate functions. -/
theorem twoChannelMax (X : Ω → ℂ) {ε_mod ε_phase : ℝ}
    (h_mod : ‖∫ ω, X ω ∂μ‖ ≤ ε_mod)
    (h_phase : ‖∫ ω, X ω ∂μ‖ ≤ ε_phase) :
    ‖∫ ω, X ω ∂μ‖ ≤ min ε_mod ε_phase :=
  le_min h_mod h_phase

omit [IsProbabilityMeasure μ] in
/-- Rate form of the two-channel bound: with the modulus channel at rate a and the phase
channel at rate λ (prefactors A, C·e^{cb²}), the decay is at the better rate. Stated as
the min of the two exponential bounds — the budget consumes exactly this shape
(budget_davies_prefactor_check_8_15 absorbs the e^{cb²} prefactor via T(b) ~ b²). -/
theorem twoChannelRate (X : Ω → ℂ) (A C a lam t : ℝ)
    (h_mod : ‖∫ ω, X ω ∂μ‖ ≤ A * Real.exp (-(a * t)))
    (h_phase : ‖∫ ω, X ω ∂μ‖ ≤ C * Real.exp (-(lam * t))) :
    ‖∫ ω, X ω ∂μ‖ ≤ min (A * Real.exp (-(a * t))) (C * Real.exp (-(lam * t))) :=
  le_min h_mod h_phase

/- ## Item-(4) spines (8/18) -/

omit [IsProbabilityMeasure μ] in
/-- Exponent bookkeeping of the three-power table: the Airy-channel rate b^{−4/3} run
for the window T = A·b^{10/3} yields exactly A·b² of suppression. -/
theorem airyWindowExponent {b A : ℝ} (hb : 0 < b) :
    b ^ (-(4:ℝ)/3) * (A * b ^ ((10:ℝ)/3)) = A * b ^ (2:ℝ) := by
  have hswap : b ^ (-(4:ℝ)/3) * (A * b ^ ((10:ℝ)/3))
      = A * (b ^ ((10:ℝ)/3) * b ^ (-(4:ℝ)/3)) := by ring
  rw [hswap, ← Real.rpow_add hb]
  norm_num

omit [IsProbabilityMeasure μ] in
/-- BUDGET WINDOW: with margin βA > c, the b² suppression beats the Davies prefactor
c·b² plus any polynomial loss K·log b, for every b past the EXPLICIT threshold
max(1, K/(βA − c)). -/
theorem budgetWindow (c K βA : ℝ) (hK : 0 ≤ K) (h : c < βA) :
    ∀ b : ℝ, max 1 (K / (βA - c)) ≤ b → c * b ^ 2 + K * Real.log b ≤ βA * b ^ 2 := by
  intro b hb
  have hb1 : (1:ℝ) ≤ b := le_trans (le_max_left _ _) hb
  have hb0 : (0:ℝ) < b := lt_of_lt_of_le one_pos hb1
  have hd : (0:ℝ) < βA - c := sub_pos.mpr h
  have hlog : Real.log b ≤ b := (Real.log_le_sub_one_of_pos hb0).trans (by linarith)
  have hKb : K / (βA - c) ≤ b := le_trans (le_max_right _ _) hb
  have hKle : K ≤ b * (βA - c) := by
    have h2 := mul_le_mul_of_nonneg_right hKb hd.le
    rwa [div_mul_cancel₀ _ hd.ne'] at h2
  have h1 : K * Real.log b ≤ K * b := mul_le_mul_of_nonneg_left hlog hK
  nlinarith [h1, hKle, hb0.le, sq_nonneg b]

omit [IsProbabilityMeasure μ] in
/-- The admissible-region claim, machine-checked: prefactor × decay ≤ 1 past the
threshold. (Instantiate βA via `airyWindowExponent`: β·b^{−4/3}·(A·b^{10/3}) = βA·b².) -/
theorem item4Admissible (c K βA : ℝ) (hK : 0 ≤ K) (h : c < βA) :
    ∀ b : ℝ, max 1 (K / (βA - c)) ≤ b →
      Real.exp (c * b ^ 2 + K * Real.log b) * Real.exp (-(βA * b ^ 2)) ≤ 1 := by
  intro b hb
  rw [← Real.exp_add]
  have hw := budgetWindow c K βA hK h b hb
  have hle : c * b ^ 2 + K * Real.log b + -(βA * b ^ 2) ≤ 0 := by linarith
  calc Real.exp (c * b ^ 2 + K * Real.log b + -(βA * b ^ 2))
      ≤ Real.exp 0 := Real.exp_le_exp.mpr hle
    _ = 1 := Real.exp_zero

section Item4Spines
/- Fresh variables: a single measurable structure (no sub-σ-algebra in scope), so
instance resolution is unambiguous for products and partitions. -/
variable {Ω₂ : Type*} [MeasurableSpace Ω₂] (ν : Measure Ω₂) [IsProbabilityMeasure ν]

omit [IsProbabilityMeasure ν] in
/-- CLASSWISE INTERLOCK: a finite measurable partition of path space with a per-class
bound on each piece yields the summed global bound. Application: classes = radial
path-classes (typical / holonomy-evading / etc.); each ε i is that class's best channel
bound (min over channels), supplied by cited per-class rate and probability estimates.
This is the structural content of "no path class evades both channels". -/
theorem classwiseInterlock {k : ℕ} (A : Fin k → Set Ω₂)
    (hmeas : ∀ i, MeasurableSet (A i))
    (hdisj : Pairwise (Function.onFun Disjoint A))
    (hcover : (⋃ i, A i) = Set.univ)
    (X : Ω₂ → ℂ) (hX : Integrable X ν)
    (ε : Fin k → ℝ) (hclass : ∀ i, ‖∫ ω in A i, X ω ∂ν‖ ≤ ε i) :
    ‖∫ ω, X ω ∂ν‖ ≤ ∑ i, ε i := by
  have hsplit : ∫ ω, X ω ∂ν = ∑ i, ∫ ω in A i, X ω ∂ν := by
    have h1 : ∫ ω, X ω ∂ν = ∫ ω in ⋃ i, A i, X ω ∂ν := by
      rw [hcover, setIntegral_univ]
    rw [h1, integral_iUnion hmeas hdisj hX.integrableOn, tsum_fintype]
  rw [hsplit]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hclass i)

/-- SPHERICAL FUBINI: the cross-path (radial) average of the spherical mean equals the
direction-average of the directional expectations — the swap behind "Y = spherical mean
of plane waves" that reduces the flat case to the classical radial input. -/
theorem sphericalFubini {S : Type*} [MeasurableSpace S] (σ : Measure S) [SFinite σ]
    (F : Ω₂ → S → ℂ) (hF : Integrable (Function.uncurry F) (ν.prod σ)) :
    ∫ ω, ∫ u, F ω u ∂σ ∂ν = ∫ u, ∫ ω, F ω u ∂ν ∂σ :=
  integral_integral_swap hF

/-- DIRECTIONAL REDUCTION: ‖E_r[Y]‖ is bounded by the direction-average of the
directional characteristic functions ‖E_r[F(·, u)]‖ — item (4)'s statement shape. -/
theorem directionalReduction {S : Type*} [MeasurableSpace S] (σ : Measure S) [SFinite σ]
    (F : Ω₂ → S → ℂ) (hF : Integrable (Function.uncurry F) (ν.prod σ)) :
    ‖∫ ω, ∫ u, F ω u ∂σ ∂ν‖ ≤ ∫ u, ‖∫ ω, F ω u ∂ν‖ ∂σ := by
  rw [sphericalFubini ν σ F hF]
  exact norm_integral_le_integral_norm _

end Item4Spines

end FriedBridgeTwoChannel
