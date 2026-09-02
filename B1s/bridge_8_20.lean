/-
THE BRIDGE — CONSOLIDATED (8/20, per Ben: one file carries the whole bridge).
Supersedes bridge_composition_8_15.lean + bridge_two_channel_8_16.lean +
gap2_block_composition_8_17.lean (archived; vault copies remain as history).
Context: obligation 1-BRIDGE of note_preflight_8_15.md; hypothesis file
hypothesis_v4_working_8_17.md; analysis ledger analysis_ledger_8_18.md.

THE BRIDGE in one paragraph: the hypothesis H is the posed uniform-in-b twisted kinetic
gap on the sphere bundle (TZ 2311.01000 display; HT 2602.12166 Conj 1(2) endpoint).
Conditioning Bismut's T*M process on its radial path r = |p| leaves an SM-type angular
process on the radial schedule; the frozen shell at radius r IS the posed-family member
b_eff = 2br³, so H's uniformity covers every shell. Two always-valid bounds compose by
MIN (no seam): the MODULUS channel (‖E[X|r]‖ ≤ C e^{−γτ}, τ = ∫γ_frozen(r_s)ds — spends
H's uniformity) and the PHASE channel (split around the composite Y = twisted spherical
mean at scheduled radius; AREA-SPREAD bounds ‖∫Y‖ — spends H's endpoint clause + the
classical radial input). Blockwise: frozen contractions compose, adiabatic errors ADD
(telescope); the classwise interlock covers evading path classes; the budget arithmetic
(machine-checked below) absorbs the Davies prefactor e^{cb²} with T(b) ~ b^{10/3}.

ZERO SORRIES, ZERO AXIOMS. Analytic inputs enter only as cited hypotheses:
  (SM-GAP)      conditional modulus bound on the clock — H's uniformity via b_eff.
  (RAD-CONC)    the clock's Laplace bound — classical radial (OU–Bessel).
  (AREA-SPREAD) oscillatory decay of the composite ‖∫Y‖ — classical radial + endpoint
                clause (twisted spherical-mean decay); stated on the COMPOSITE (polar
                decoupling FAILS: phase_lemma_model_tests_8_16.md).
  (ADIABATIC)   per-block ‖S_j − F_j‖ — Duhamel + radial oscillation (L ≪ b²).
  (H-FROZEN)    per-block contraction in the renormed space — discharged by the posed
                form's semigroup grade + polynomial prefactor (V4 file §1b).
  (FK/LDP)      the 1D radial eigenvalue facts — item4_composition_lab_8_17.md,
                verified numerically; Mathlib lacks diffusion-FK/LDP theory.

CONTENTS (proof-order):
  §1 CHANNELS — towerModulus, modulusComposition, rateComposition (modulus channel);
     phaseChannel, phaseChannelCond (phase channel, split around Y);
     twoChannelMax, twoChannelRate (the min — the retired "seam" is one line).
  §2 BLOCKS — normProdLeOne, blockContraction, adiabaticTelescope, gap2Spine
     (frozen-block composition; per-block errors ADD, never compound).
  §3 BUDGET — airyWindowExponent, budgetWindow, item4Admissible (admissible region
     machine-checked; explicit threshold b₀ = max(1, K/(βA − c))).
  §4 ITEM-4 — classwiseInterlock (partition min-composition), sphericalFubini,
     directionalReduction (the swap behind Y = spherical mean).
-/
import Mathlib

set_option linter.style.header false

namespace FriedBridge

open MeasureTheory

/-! ### §1 CHANNELS -/
section Channels

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {m : MeasurableSpace Ω}

/-- Tower-modulus inequality: the disintegration step. `m` is the radial σ-algebra;
`μ[X|m]` is the SM-side conditional expectation on the radial clock. -/
theorem towerModulus (hm : m ≤ m₀) (X : Ω → ℂ) :
    ‖∫ ω, X ω ∂μ‖ ≤ ∫ ω, ‖(μ[X | m]) ω‖ ∂μ := by
  rw [← integral_condExp hm]
  exact norm_integral_le_integral_norm _

/-- MODULUS channel: conditional gap bound (SM-GAP) + radial averaging (RAD-CONC)
⇒ decay of the full expectation. -/
theorem modulusComposition (hm : m ≤ m₀) (X : Ω → ℂ) (B : Ω → ℝ)
    (hB : Integrable B μ)
    (hgap : ∀ᵐ ω ∂μ, ‖(μ[X | m]) ω‖ ≤ B ω)
    {ε : ℝ} (hconc : ∫ ω, B ω ∂μ ≤ ε) :
    ‖∫ ω, X ω ∂μ‖ ≤ ε :=
  le_trans (towerModulus μ hm X)
    (le_trans (integral_mono_ae integrable_condExp.norm hB hgap) hconc)

/-- Rate form of the modulus channel: SM gap at clock rate γ on the radial clock τ,
plus the clock's Laplace bound. The statement shape the budget consumes. -/
theorem rateComposition (hm : m ≤ m₀) (X : Ω → ℂ) (τ : Ω → ℝ)
    (C C' γ lam t : ℝ)
    (hint : Integrable (fun ω => C * Real.exp (-(γ * τ ω))) μ)
    (hgap : ∀ᵐ ω ∂μ, ‖(μ[X | m]) ω‖ ≤ C * Real.exp (-(γ * τ ω)))
    (hconc : ∫ ω, C * Real.exp (-(γ * τ ω)) ∂μ ≤ C' * Real.exp (-(lam * t))) :
    ‖∫ ω, X ω ∂μ‖ ≤ C' * Real.exp (-(lam * t)) :=
  modulusComposition μ hm X _ hint hgap hconc

omit [IsProbabilityMeasure μ] in
/-- PHASE channel, plain form: split X into the composite radial functional Y (the
twisted spherical mean at scheduled radius) plus a remainder. (AREA-SPREAD) bounds
‖∫Y‖; the remainder integral is the mixing-channel object (flip corrections). -/
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

/-- PHASE channel, conditional form: the flip-correction remainder measured at the
conditional level, ‖μ[X|m] − Y‖ ≤ B pointwise with ∫B ≤ ε₁ (B, Y radial functionals). -/
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
bound is their min — the retired "seam/coverage obligation" is this one line. -/
theorem twoChannelMax (X : Ω → ℂ) {ε_mod ε_phase : ℝ}
    (h_mod : ‖∫ ω, X ω ∂μ‖ ≤ ε_mod)
    (h_phase : ‖∫ ω, X ω ∂μ‖ ≤ ε_phase) :
    ‖∫ ω, X ω ∂μ‖ ≤ min ε_mod ε_phase :=
  le_min h_mod h_phase

omit [IsProbabilityMeasure μ] in
/-- Rate form of the two-channel bound: decay at the better rate; the budget consumes
exactly this shape. -/
theorem twoChannelRate (X : Ω → ℂ) (A C a lam t : ℝ)
    (h_mod : ‖∫ ω, X ω ∂μ‖ ≤ A * Real.exp (-(a * t)))
    (h_phase : ‖∫ ω, X ω ∂μ‖ ≤ C * Real.exp (-(lam * t))) :
    ‖∫ ω, X ω ∂μ‖ ≤ min (A * Real.exp (-(a * t))) (C * Real.exp (-(lam * t))) :=
  le_min h_mod h_phase

end Channels

/-! ### §2 BLOCKS -/
section Blocks

variable {A : Type*} [NormedRing A] [NormOneClass A]

/-- Products of contractions are contractions. -/
theorem normProdLeOne : ∀ (l : List A), (∀ x ∈ l, ‖x‖ ≤ 1) → ‖l.prod‖ ≤ 1
  | [], _ => by simp
  | x :: xs, h => by
    have hx : ‖x‖ ≤ 1 := h x (by simp)
    have ih : ‖xs.prod‖ ≤ 1 :=
      normProdLeOne xs fun y hy => h y (by simp [hy])
    calc ‖(x :: xs).prod‖ = ‖x * xs.prod‖ := by rw [List.prod_cons]
      _ ≤ ‖x‖ * ‖xs.prod‖ := norm_mul_le _ _
      _ ≤ 1 * 1 := mul_le_mul hx ih (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1

/-- Per-block rates compose: pairs (F_j, g_j) with ‖F_j‖ ≤ exp(−g_j) give
‖∏F_j‖ ≤ exp(−Σg_j). (g_j = γ(b_eff(r̄_j))·L in the application; H-FROZEN.) -/
theorem blockContraction : ∀ (p : List (A × ℝ)),
    (∀ q ∈ p, ‖q.1‖ ≤ Real.exp (-q.2)) →
    ‖(p.map Prod.fst).prod‖ ≤ Real.exp (-(p.map Prod.snd).sum)
  | [], _ => by simp
  | q :: ps, h => by
    have hq : ‖q.1‖ ≤ Real.exp (-q.2) := h q (by simp)
    have ih := blockContraction ps fun w hw => h w (by simp [hw])
    calc ‖((q :: ps).map Prod.fst).prod‖
        = ‖q.1 * (ps.map Prod.fst).prod‖ := by simp
      _ ≤ ‖q.1‖ * ‖(ps.map Prod.fst).prod‖ := norm_mul_le _ _
      _ ≤ Real.exp (-q.2) * Real.exp (-(ps.map Prod.snd).sum) :=
          mul_le_mul hq ih (norm_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (-((q :: ps).map Prod.snd).sum) := by
          rw [← Real.exp_add]; congr 1; simp; ring

/-- Adiabatic telescope: for two equal-length lists of contractions, the product
difference is bounded by the SUM of factor differences — per-block errors add, they
never compound. The entire adiabatic bookkeeping of the block route (ADIABATIC). -/
theorem adiabaticTelescope : ∀ (s f : List A), s.length = f.length →
    (∀ x ∈ s, ‖x‖ ≤ 1) → (∀ x ∈ f, ‖x‖ ≤ 1) →
    ‖s.prod - f.prod‖ ≤ (List.zipWith (fun x y => ‖x - y‖) s f).sum
  | [], [], _, _, _ => by simp
  | [], _ :: _, h, _, _ => by simp at h
  | _ :: _, [], h, _, _ => by simp at h
  | x :: xs, y :: ys, h, hs, hf => by
    have hlen : xs.length = ys.length := by simpa using h
    have hx : ‖x‖ ≤ 1 := hs x (by simp)
    have hys : ‖ys.prod‖ ≤ 1 := normProdLeOne ys fun z hz => hf z (by simp [hz])
    have ih := adiabaticTelescope xs ys hlen
      (fun z hz => hs z (by simp [hz])) (fun z hz => hf z (by simp [hz]))
    have key : (x :: xs).prod - (y :: ys).prod
        = x * (xs.prod - ys.prod) + (x - y) * ys.prod := by
      simp only [List.prod_cons]; noncomm_ring
    calc ‖(x :: xs).prod - (y :: ys).prod‖
        = ‖x * (xs.prod - ys.prod) + (x - y) * ys.prod‖ := by rw [key]
      _ ≤ ‖x * (xs.prod - ys.prod)‖ + ‖(x - y) * ys.prod‖ := norm_add_le _ _
      _ ≤ ‖x‖ * ‖xs.prod - ys.prod‖ + ‖x - y‖ * ‖ys.prod‖ :=
          add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ 1 * (List.zipWith (fun a b => ‖a - b‖) xs ys).sum + ‖x - y‖ * 1 :=
          add_le_add (mul_le_mul hx ih (norm_nonneg _) zero_le_one)
            (mul_le_mul_of_nonneg_left hys (norm_nonneg _))
      _ = ‖x - y‖ + (List.zipWith (fun a b => ‖a - b‖) xs ys).sum := by ring
      _ = (List.zipWith (fun a b => ‖a - b‖) (x :: xs) (y :: ys)).sum := by simp

/-- THE GAP-2 SPINE, assembled: true blocks S_j (contractions), frozen reference blocks
F_j with rates g_j (H-FROZEN), per-block adiabatic errors (ADIABATIC) ⇒ the conditioned
propagator obeys the composed frozen rate up to the summed adiabatic error. -/
theorem gap2Spine (s : List A) (p : List (A × ℝ))
    (hlen : s.length = p.length)
    (hs : ∀ x ∈ s, ‖x‖ ≤ 1)
    (hf1 : ∀ q ∈ p, ‖q.1‖ ≤ 1)
    (hf2 : ∀ q ∈ p, ‖q.1‖ ≤ Real.exp (-q.2)) :
    ‖s.prod‖ ≤ Real.exp (-(p.map Prod.snd).sum)
      + (List.zipWith (fun x y => ‖x - y‖) s (p.map Prod.fst)).sum := by
  have hlen' : s.length = (p.map Prod.fst).length := by simpa using hlen
  have hf1' : ∀ x ∈ p.map Prod.fst, ‖x‖ ≤ 1 := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
    exact hf1 q hq
  have tri : ‖s.prod‖ ≤ ‖s.prod - (p.map Prod.fst).prod‖ + ‖(p.map Prod.fst).prod‖ := by
    calc ‖s.prod‖ = ‖(s.prod - (p.map Prod.fst).prod) + (p.map Prod.fst).prod‖ := by
          rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  calc ‖s.prod‖
      ≤ ‖s.prod - (p.map Prod.fst).prod‖ + ‖(p.map Prod.fst).prod‖ := tri
    _ ≤ (List.zipWith (fun x y => ‖x - y‖) s (p.map Prod.fst)).sum
        + Real.exp (-(p.map Prod.snd).sum) :=
        add_le_add (adiabaticTelescope s (p.map Prod.fst) hlen' hs hf1')
          (blockContraction p hf2)
    _ = _ := by ring

end Blocks

/-! ### §3 BUDGET (pure real arithmetic — the admissible region, machine-checked) -/

/-- Exponent bookkeeping of the three-power table: the Airy-channel rate b^{−4/3} run
for the window T = A·b^{10/3} yields exactly A·b² of suppression. -/
theorem airyWindowExponent {b A : ℝ} (hb : 0 < b) :
    b ^ (-(4:ℝ)/3) * (A * b ^ ((10:ℝ)/3)) = A * b ^ (2:ℝ) := by
  have hswap : b ^ (-(4:ℝ)/3) * (A * b ^ ((10:ℝ)/3))
      = A * (b ^ ((10:ℝ)/3) * b ^ (-(4:ℝ)/3)) := by ring
  rw [hswap, ← Real.rpow_add hb]
  norm_num

/-- BUDGET WINDOW: with margin βA > c, the b² suppression beats the Davies prefactor
c·b² plus any polynomial loss K·log b, past the EXPLICIT threshold max(1, K/(βA − c)). -/
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

/-- The admissible-region claim: prefactor × decay ≤ 1 past the threshold.
(Instantiate βA via `airyWindowExponent`: β·b^{−4/3}·(A·b^{10/3}) = βA·b².) -/
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

/-! ### §4 ITEM-4 (partition interlock + the Y-reduction swap) -/
section Item4

variable {Ω₂ : Type*} [MeasurableSpace Ω₂] (ν : Measure Ω₂) [IsProbabilityMeasure ν]

omit [IsProbabilityMeasure ν] in
/-- CLASSWISE INTERLOCK: a finite measurable partition of path space with a per-class
bound on each piece yields the summed global bound. Classes = radial path-classes
(typical / holonomy-evading); each ε i is that class's best channel bound (min over
channels), supplied by cited per-class rate and probability estimates. The structural
content of "no path class evades both channels". -/
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

end Item4

end FriedBridge
