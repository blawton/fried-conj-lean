/-
B1-SPECTRAL — axiom-quarantined Lean skeleton (8/12)

Companions: b2_remainder_lean_layer.md §8a (K11/K12), b1_summability_model_test_8_12.md §6
(the moral: spectral pinning by mass conservation), goal_conditional_reduction_8_12.md §3.

WHAT THIS FILE IS: the complete derivation tree of B1's aggregate summability clause from
five VEHICLE axioms, with every cargo step proved (zero `sorry`s). The axioms are the pieces
not Lean-checkable on any near horizon, each tagged with what supplies it mathematically:

  V1  heat-trace formula at finite b        (kinetic spectral theory — Drouot-side)
  V2  endpoint trace formula = orbit data   (DZ flat trace + noise-independence, pp8 §4(2))
  V3  mass conservation pins the top        (Liouville invariance at every b — identity;
                                             finite-dim cargo version PROVED below as K12)
  V4  the uniform gap                       (THE REDUCTION'S HYPOTHESIS + L1 at endpoint)
  V5  summable resonance drift              (stochastic stability, quantitative)

MAIN RESULTS (proved):
  b1_per_length : ‖heatTrace b (n+1) − orbitSum (n+1)‖ ≤ (n+1)·θ^n·D b      (b ≥ b₀)
  b1_aggregate  : Σ_{n<L} ‖heatTrace b (n+1) − orbitSum (n+1)‖ ≤ (1−θ)⁻²·D b (any L)
i.e. B1's aggregate clause holds with the SAME b-decay rate as the drift, uniformly in the
window length — the summability-against-e^{hℓ} problem never appears, because pinning +
gap convert it into a geometric series. This is the Lean form of the model test's moral.

AUDIT CRITERION: `#print axioms b1_aggregate` must list exactly V1–V5 (plus Lean built-ins).
-/
import Mathlib

set_option linter.style.header false

open scoped BigOperators
open Matrix

namespace FriedB1Spectral

/-! ## Cargo 1 (K11 core): telescoping power bound.
`ℓ+1` form throughout — no natural subtraction anywhere. -/

lemma pow_succ_sub_bound (x y : ℂ) (m : ℝ) (hx : ‖x‖ ≤ m) (hy : ‖y‖ ≤ m) :
    ∀ n : ℕ, ‖x ^ (n + 1) - y ^ (n + 1)‖ ≤ (n + 1) * m ^ n * ‖x - y‖ := by
  have hm : 0 ≤ m := le_trans (norm_nonneg x) hx
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have key : x ^ (n + 2) - y ^ (n + 2)
          = x ^ (n + 1) * (x - y) + (x ^ (n + 1) - y ^ (n + 1)) * y := by ring
      have h1 : ‖x ^ (n + 1) * (x - y)‖ ≤ m ^ (n + 1) * ‖x - y‖ := by
        rw [norm_mul, norm_pow]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (norm_nonneg x) hx (n + 1)) (norm_nonneg _)
      have h2 : ‖(x ^ (n + 1) - y ^ (n + 1)) * y‖
          ≤ ((n + 1) * m ^ n * ‖x - y‖) * m := by
        rw [norm_mul]
        exact mul_le_mul ih hy (norm_nonneg y) (by positivity)
      calc ‖x ^ (n + 2) - y ^ (n + 2)‖
          ≤ ‖x ^ (n + 1) * (x - y)‖ + ‖(x ^ (n + 1) - y ^ (n + 1)) * y‖ := by
            rw [key]; exact norm_add_le _ _
        _ ≤ m ^ (n + 1) * ‖x - y‖ + ((n + 1) * m ^ n * ‖x - y‖) * m := add_le_add h1 h2
        _ = ((n + 1 : ℕ) + 1) * m ^ (n + 1) * ‖x - y‖ := by push_cast; ring

/-! ## Cargo 2 (K12, finite-dimensional): mass conservation pins the top.
The cargo demonstration of WHY axiom V3 is an identity: any finite kernel whose columns
sum to one has 1 as an eigenvalue (det(M − 1) = 0, via the all-ones null vector of the
transpose). -/

lemma det_sub_one_eq_zero_of_colsum_one {n : ℕ} [NeZero n]
    (M : Matrix (Fin n) (Fin n) ℂ) (h : ∀ j, ∑ i, M i j = 1) :
    (M - 1).det = 0 := by
  have hdet : ((M - 1).transpose).det = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    refine ⟨fun _ => 1, ?_, ?_⟩
    · intro h0
      exact one_ne_zero (congrFun h0 ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩)
    · funext i
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.sub_apply,
        Matrix.one_apply, mul_one, Pi.zero_apply]
      rw [Finset.sum_sub_distrib, h i]
      simp
  rwa [Matrix.det_transpose] at hdet

/-! ## Cargo 3: the geometric aggregate  Σ_{n<L} (n+1)θ^n ≤ (1−θ)⁻². -/

lemma sum_succ_mul_geometric_le {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) (L : ℕ) :
    ∑ n ∈ Finset.range L, ((n + 1 : ℝ) * θ ^ n) ≤ (1 - θ)⁻¹ ^ 2 := by
  have hn : ‖θ‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg h0]
  have hA : HasSum (fun n : ℕ => (n : ℝ) * θ ^ n) (θ / (1 - θ) ^ 2) :=
    hasSum_coe_mul_geometric_of_norm_lt_one hn
  have hB : HasSum (fun n : ℕ => θ ^ n) ((1 - θ)⁻¹) :=
    hasSum_geometric_of_lt_one h0 h1
  have hAB : HasSum (fun n : ℕ => ((n : ℝ) + 1) * θ ^ n)
      (θ / (1 - θ) ^ 2 + (1 - θ)⁻¹) := by
    simpa [add_mul] using hA.add hB
  have hval : θ / (1 - θ) ^ 2 + (1 - θ)⁻¹ = (1 - θ)⁻¹ ^ 2 := by
    have hne : (1 : ℝ) - θ ≠ 0 := by linarith
    field_simp
    ring
  have hsum := Summable.sum_le_tsum (Finset.range L)
    (fun i _ => by positivity) hAB.summable
  calc ∑ n ∈ Finset.range L, ((n + 1 : ℝ) * θ ^ n)
      ≤ ∑' n : ℕ, ((n : ℝ) + 1) * θ ^ n := by
        simpa [add_comm] using hsum
    _ = (1 - θ)⁻¹ ^ 2 := by rw [hAB.tsum_eq, hval]

/-! ## The vehicle, quarantined: five axioms.
Everything below this block is PROVED; nothing above it is provable in Lean this decade. -/

/-- Threshold parameter of the family (large-`b` regime). -/
axiom b₀ : ℝ

/-- The uniform subleading radius. `hθ` packages 0 ≤ θ < 1 — the GAP. -/
axiom θ : ℝ
axiom hθ : 0 ≤ θ ∧ θ < 1

/-- Resonances of the ρ-twisted kinetic (Bismut-family) operator at parameter b;
index 0 is the leading one. VEHICLE: kinetic spectral theory (Drouot-side). -/
axiom kineticRes : ℝ → ℕ → ℂ

/-- Endpoint (Pollicott–Ruelle) resonances of the twisted geodesic flow. VEHICLE. -/
axiom endpointRes : ℕ → ℂ

/-- Heat-trace side of B1 at parameter b, length ℓ. VEHICLE object. -/
axiom heatTrace : ℝ → ℕ → ℂ

/-- Orbit side of B1: the per-orbit Gaussian/zeta data sum (b-free by the
noise-independence identity, pp8 §4(2)). VEHICLE object. -/
axiom orbitSum : ℕ → ℂ

/-- V1 (trace formula, finite b): the heat trace is the resonance power sum.
VEHICLE: kinetic trace theory across form degrees. -/
axiom V1 : ∀ b : ℝ, b₀ ≤ b → ∀ n : ℕ,
  HasSum (fun i => kineticRes b i ^ (n + 1)) (heatTrace b (n + 1))

/-- V2 (endpoint trace formula = orbit data): flat trace equals the resonance power sum
AND the noise-independent orbit sum. VEHICLE: Dyatlov–Zworski flat-trace theory; the
orbit-data identification is pp8 §4(2). -/
axiom V2 : ∀ n : ℕ, HasSum (fun i => endpointRes i ^ (n + 1)) (orbitSum (n + 1))

/-- V3 (mass conservation pins the top, at every b and at the endpoint). Analytically an
IDENTITY (Liouville invariance; Lemma A's mechanism); finite-dim cargo shadow:
`det_sub_one_eq_zero_of_colsum_one`. -/
axiom V3 : (∀ b : ℝ, b₀ ≤ b → kineticRes b 0 = 1) ∧ endpointRes 0 = 1

/-- V4 (THE GAP — the conditional reduction's hypothesis, plus L1 at the endpoint):
all subleading resonances lie in the θ-disc, uniformly in b. -/
axiom V4 : (∀ b : ℝ, b₀ ≤ b → ∀ i : ℕ, ‖kineticRes b (i + 1)‖ ≤ θ) ∧
  (∀ i : ℕ, ‖endpointRes (i + 1)‖ ≤ θ)

/-- Drift budget at parameter b (analytically D b = O(b^{-p})). -/
axiom D : ℝ → ℝ

/-- V5 (quantitative stochastic stability): total resonance drift ≤ D b. Stated over the
FULL index — the i = 0 term is zero by V3, so including it is free and avoids index
shifts. VEHICLE: the convergence input the compactified route already carries. -/
axiom V5 : ∀ b : ℝ, b₀ ≤ b →
  Summable (fun i => ‖kineticRes b i - endpointRes i‖) ∧
  (∑' i : ℕ, ‖kineticRes b i - endpointRes i‖) ≤ D b

/-! ## The assembly (proved) -/

/-- Per-length B1 bound: pinning kills the leading term, the gap prices the rest. -/
theorem b1_per_length (b : ℝ) (hb : b₀ ≤ b) (n : ℕ) :
    ‖heatTrace b (n + 1) - orbitSum (n + 1)‖ ≤ (n + 1) * θ ^ n * D b := by
  obtain ⟨V3k, V3e⟩ := V3
  obtain ⟨V4k, V4e⟩ := V4
  obtain ⟨V5s, V5b⟩ := V5 b hb
  have hθ0 : 0 ≤ θ := hθ.1
  set f : ℕ → ℂ := fun i => kineticRes b i ^ (n + 1) - endpointRes i ^ (n + 1) with hf
  have hsub : HasSum f (heatTrace b (n + 1) - orbitSum (n + 1)) :=
    (V1 b hb n).sub (V2 n)
  -- termwise bound; at i = 0 both sides vanish by pinning
  have hterm : ∀ i : ℕ, ‖f i‖
      ≤ ((n : ℝ) + 1) * θ ^ n * ‖kineticRes b i - endpointRes i‖ := by
    intro i
    match i with
    | 0 =>
        simp [hf, V3k b hb, V3e]
    | (i + 1) =>
        exact pow_succ_sub_bound _ _ θ (V4k b hb i) (V4e i) n
  have hbound : Summable (fun i =>
      ((n : ℝ) + 1) * θ ^ n * ‖kineticRes b i - endpointRes i‖) :=
    V5s.mul_left _
  have hnorm : Summable (fun i => ‖f i‖) :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) hterm hbound
  have hc : (0 : ℝ) ≤ ((n : ℝ) + 1) * θ ^ n :=
    mul_nonneg (by positivity) (pow_nonneg hθ0 n)
  have h1 : ‖heatTrace b (n + 1) - orbitSum (n + 1)‖ ≤ ∑' i, ‖f i‖ := by
    rw [← hsub.tsum_eq]
    exact norm_tsum_le_tsum_norm hnorm
  have h3 : (∑' i, ‖f i‖) ≤ ((n : ℝ) + 1) * θ ^ n * D b := by
    calc (∑' i, ‖f i‖)
        ≤ ∑' i, ((n : ℝ) + 1) * θ ^ n * ‖kineticRes b i - endpointRes i‖ :=
          Summable.tsum_le_tsum hterm hnorm hbound
      _ = ((n : ℝ) + 1) * θ ^ n * ∑' i, ‖kineticRes b i - endpointRes i‖ :=
          tsum_mul_left
      _ ≤ ((n : ℝ) + 1) * θ ^ n * D b := mul_le_mul_of_nonneg_left V5b hc
  calc ‖heatTrace b (n + 1) - orbitSum (n + 1)‖
      ≤ ∑' i, ‖f i‖ := h1
    _ ≤ ((n : ℝ) + 1) * θ ^ n * D b := h3
    _ = (n + 1) * θ ^ n * D b := by ring

/-- B1's aggregate summability clause: the total error over ALL window lengths is one
drift budget times a geometric constant. The e^{hℓ} class count never appears — pinning
plus the gap replace orbit-counting with a geometric series. -/
theorem b1_aggregate (b : ℝ) (hb : b₀ ≤ b) (hD : 0 ≤ D b) (L : ℕ) :
    ∑ n ∈ Finset.range L, ‖heatTrace b (n + 1) - orbitSum (n + 1)‖
      ≤ (1 - θ)⁻¹ ^ 2 * D b := by
  have hstep : ∀ n ∈ Finset.range L,
      ‖heatTrace b (n + 1) - orbitSum (n + 1)‖ ≤ ((n + 1 : ℝ) * θ ^ n) * D b := by
    intro n _
    have := b1_per_length b hb n
    calc ‖heatTrace b (n + 1) - orbitSum (n + 1)‖
        ≤ (n + 1) * θ ^ n * D b := this
      _ = ((n + 1 : ℝ) * θ ^ n) * D b := by ring
  calc ∑ n ∈ Finset.range L, ‖heatTrace b (n + 1) - orbitSum (n + 1)‖
      ≤ ∑ n ∈ Finset.range L, ((n + 1 : ℝ) * θ ^ n) * D b :=
        Finset.sum_le_sum hstep
    _ = (∑ n ∈ Finset.range L, ((n + 1 : ℝ) * θ ^ n)) * D b := by
        rw [← Finset.sum_mul]
    _ ≤ (1 - θ)⁻¹ ^ 2 * D b :=
        mul_le_mul_of_nonneg_right (sum_succ_mul_geometric_le hθ.1 hθ.2 L) hD

/-!
AUDIT NOTE. `#print axioms b1_aggregate` should list exactly V1–V5 (with b₀, θ, hθ, D,
kineticRes, endpointRes, heatTrace, orbitSum as the opaque vehicle constants) plus Lean's
built-ins. If any OTHER axiom appears, the assembly has a hole. Mathematical reading:
inside the conditional reduction (where V4 is hypothesis and V3 is an identity), B1's
remaining debt is exactly V1 + V2 + V5 — trace formulas and quantitative stochastic
stability, the named bookkeeping of b1_summability_model_test_8_12.md §6.
-/

#print axioms b1_aggregate

/-! ## The twisted case (acyclic ρ) — NO pinning axiom needed.
The determinant passage's actual objects are twisted by an acyclic unitary ρ: there is no
invariant section, hence no leading resonance 1 on EITHER side — the entire twisted
spectrum sits inside the θ-disc (that is precisely the gap hypothesis at s = 0). So the
twisted assembly consumes only gap + drift: V3 has no analogue here, and the scalar
version above is the toy-faithful demonstration (mass is conserved in the scalar shadow)
plus whatever scalar-shadow bookkeeping the passage's normalization needs.
AUDIT: `#print axioms b1_aggregate_twisted` must show W1/W2/W4/W5 and NO pinning axiom. -/

/-- Twisted kinetic resonances (acyclic ρ): no distinguished leading index. VEHICLE. -/
axiom kineticResTw : ℝ → ℕ → ℂ

/-- Twisted endpoint resonances. VEHICLE. -/
axiom endpointResTw : ℕ → ℂ

/-- Twisted heat trace. VEHICLE object. -/
axiom heatTraceTw : ℝ → ℕ → ℂ

/-- Twisted orbit-data sum. VEHICLE object. -/
axiom orbitSumTw : ℕ → ℂ

/-- W1: twisted trace formula at finite b. VEHICLE. -/
axiom W1 : ∀ b : ℝ, b₀ ≤ b → ∀ n : ℕ,
  HasSum (fun i => kineticResTw b i ^ (n + 1)) (heatTraceTw b (n + 1))

/-- W2: twisted endpoint trace formula = orbit data. VEHICLE. -/
axiom W2 : ∀ n : ℕ, HasSum (fun i => endpointResTw i ^ (n + 1)) (orbitSumTw (n + 1))

/-- W4 (THE GAP, twisted form): ALL twisted resonances — index 0 included — lie in the
θ-disc, uniformly in b. This is where acyclicity is spent: no invariant section means no
resonance survives at the top. -/
axiom W4 : (∀ b : ℝ, b₀ ≤ b → ∀ i : ℕ, ‖kineticResTw b i‖ ≤ θ) ∧
  (∀ i : ℕ, ‖endpointResTw i‖ ≤ θ)

/-- W5: twisted resonance drift ≤ D b. VEHICLE. -/
axiom W5 : ∀ b : ℝ, b₀ ≤ b →
  Summable (fun i => ‖kineticResTw b i - endpointResTw i‖) ∧
  (∑' i : ℕ, ‖kineticResTw b i - endpointResTw i‖) ≤ D b

/-- Twisted per-length bound: gap + drift alone — no pinning, no case split at i = 0. -/
theorem b1_per_length_twisted (b : ℝ) (hb : b₀ ≤ b) (n : ℕ) :
    ‖heatTraceTw b (n + 1) - orbitSumTw (n + 1)‖ ≤ (n + 1) * θ ^ n * D b := by
  obtain ⟨W4k, W4e⟩ := W4
  obtain ⟨W5s, W5b⟩ := W5 b hb
  have hθ0 : 0 ≤ θ := hθ.1
  set f : ℕ → ℂ := fun i => kineticResTw b i ^ (n + 1) - endpointResTw i ^ (n + 1) with hf
  have hsub : HasSum f (heatTraceTw b (n + 1) - orbitSumTw (n + 1)) :=
    (W1 b hb n).sub (W2 n)
  have hterm : ∀ i : ℕ, ‖f i‖
      ≤ ((n : ℝ) + 1) * θ ^ n * ‖kineticResTw b i - endpointResTw i‖ :=
    fun i => pow_succ_sub_bound _ _ θ (W4k b hb i) (W4e i) n
  have hbound : Summable (fun i =>
      ((n : ℝ) + 1) * θ ^ n * ‖kineticResTw b i - endpointResTw i‖) :=
    W5s.mul_left _
  have hnorm : Summable (fun i => ‖f i‖) :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) hterm hbound
  have hc : (0 : ℝ) ≤ ((n : ℝ) + 1) * θ ^ n :=
    mul_nonneg (by positivity) (pow_nonneg hθ0 n)
  have h1 : ‖heatTraceTw b (n + 1) - orbitSumTw (n + 1)‖ ≤ ∑' i, ‖f i‖ := by
    rw [← hsub.tsum_eq]
    exact norm_tsum_le_tsum_norm hnorm
  have h3 : (∑' i, ‖f i‖) ≤ ((n : ℝ) + 1) * θ ^ n * D b := by
    calc (∑' i, ‖f i‖)
        ≤ ∑' i, ((n : ℝ) + 1) * θ ^ n * ‖kineticResTw b i - endpointResTw i‖ :=
          Summable.tsum_le_tsum hterm hnorm hbound
      _ = ((n : ℝ) + 1) * θ ^ n * ∑' i, ‖kineticResTw b i - endpointResTw i‖ :=
          tsum_mul_left
      _ ≤ ((n : ℝ) + 1) * θ ^ n * D b := mul_le_mul_of_nonneg_left W5b hc
  calc ‖heatTraceTw b (n + 1) - orbitSumTw (n + 1)‖
      ≤ ∑' i, ‖f i‖ := h1
    _ ≤ ((n : ℝ) + 1) * θ ^ n * D b := h3
    _ = (n + 1) * θ ^ n * D b := by ring

/-- Twisted aggregate clause — the form the reduction actually consumes. -/
theorem b1_aggregate_twisted (b : ℝ) (hb : b₀ ≤ b) (hD : 0 ≤ D b) (L : ℕ) :
    ∑ n ∈ Finset.range L, ‖heatTraceTw b (n + 1) - orbitSumTw (n + 1)‖
      ≤ (1 - θ)⁻¹ ^ 2 * D b := by
  have hstep : ∀ n ∈ Finset.range L,
      ‖heatTraceTw b (n + 1) - orbitSumTw (n + 1)‖ ≤ ((n + 1 : ℝ) * θ ^ n) * D b := by
    intro n _
    have := b1_per_length_twisted b hb n
    calc ‖heatTraceTw b (n + 1) - orbitSumTw (n + 1)‖
        ≤ (n + 1) * θ ^ n * D b := this
      _ = ((n + 1 : ℝ) * θ ^ n) * D b := by ring
  calc ∑ n ∈ Finset.range L, ‖heatTraceTw b (n + 1) - orbitSumTw (n + 1)‖
      ≤ ∑ n ∈ Finset.range L, ((n + 1 : ℝ) * θ ^ n) * D b :=
        Finset.sum_le_sum hstep
    _ = (∑ n ∈ Finset.range L, ((n + 1 : ℝ) * θ ^ n)) * D b := by
        rw [← Finset.sum_mul]
    _ ≤ (1 - θ)⁻¹ ^ 2 * D b :=
        mul_le_mul_of_nonneg_right (sum_succ_mul_geometric_le hθ.1 hθ.2 L) hD

#print axioms b1_aggregate_twisted

/-! ## B1 WINDOW COMPOSITION (8/28, per Ben: "why can't it be lean-formalized?")

The last unformalized assembly step of B1-spectral — the window/range bookkeeping —
and formalizing it RECORDS A CORRECTION: at spectral grade, under H (θ b-uniform,
axiom V4), `b1_aggregate`'s bound (1−θ)⁻²·D b holds for EVERY window length L, so
the "range condition ℓ ≲ b^{10/3}" is NOT a condition of this route at all — it
belongs to the orbit-side (bridge-channel-rate) bookkeeping, which the note keeps
as the hedge/second proof. Consequences: (i) the killer item "B1@b^{10/3}"
re-attaches — the spectral route's residual inputs are exactly D b → 0 (V5,
quantitative: the same Drouot read as `hpt`) and the V1/V2 trace-formula citations;
(ii) the budget's exponent arithmetic survives below as `window_race`, the formal
home of the range condition for a DEGRADED-gap regime θ(b) = 1 − c·b^{−p} — needed
only for sharpness commentary or if H's uniformity is ever weakened. -/

/-- B1 TOTAL ERROR VANISHES, uniformly in the window: if the drift budget D b → 0
(and D is eventually nonnegative), then for every ε > 0, eventually in b, the
aggregate B1 error is < ε SIMULTANEOUSLY for all window lengths L. The window never
re-enters: this is `b1_aggregate` + the limit, nothing else. Consumes V1–V5 (via
`b1_aggregate`) plus the two D-hypotheses. -/
theorem b1_total_error_vanishes
    (hD0 : Filter.Tendsto D Filter.atTop (nhds 0))
    (hDpos : ∀ᶠ b in Filter.atTop, 0 ≤ D b) :
    ∀ ε > 0, ∀ᶠ b in Filter.atTop, ∀ L : ℕ,
      (∑ n ∈ Finset.range L, ‖heatTrace b (n + 1) - orbitSum (n + 1)‖) < ε := by
  intro ε hε
  have hconv : Filter.Tendsto (fun b => (1 - θ)⁻¹ ^ 2 * D b) Filter.atTop (nhds 0) := by
    have h := (tendsto_const_nhds (x := (1 - θ)⁻¹ ^ 2)).mul hD0
    rwa [mul_zero] at h
  have hsmall : ∀ᶠ b in Filter.atTop, (1 - θ)⁻¹ ^ 2 * D b < ε :=
    hconv.eventually (gt_mem_nhds hε)
  filter_upwards [hsmall, hDpos, Filter.eventually_ge_atTop b₀] with b h1 h2 h3
  intro L
  exact lt_of_le_of_lt (b1_aggregate b h3 h2 L) h1

/-- THE RANGE CONDITION, formalized (degraded-gap regime only): if the gap closes
polynomially, θ(b) = 1 − c·b^{−p}, while the drift decays like C·b^{−p′}, then the
composed aggregate bound (1−θ(b))⁻²·(C·b^{−p′}) vanishes iff the exponents race the
right way — the hypothesis is exactly **p′ > 2p**, the budget arithmetic of
item4_composition_lab_8_17 §4 as a theorem. Pure arithmetic: no axioms consumed.
Under H this theorem is NOT needed (θ is b-uniform and `b1_total_error_vanishes`
applies); it is the sharpness-side record of what failure of uniformity would cost. -/
theorem window_race (c C p p' : ℝ) (hc : 0 < c) (hrace : 2 * p < p') :
    Filter.Tendsto
      (fun b : ℝ => (1 - (1 - c * b ^ (-p)))⁻¹ ^ 2 * (C * b ^ (-p')))
      Filter.atTop (nhds 0) := by
  have key : ∀ᶠ b : ℝ in Filter.atTop,
      (C / c ^ 2) * b ^ (-(p' - 2 * p))
        = (1 - (1 - c * b ^ (-p)))⁻¹ ^ 2 * (C * b ^ (-p')) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with b hb
    have h1 : 1 - (1 - c * b ^ (-p)) = c * b ^ (-p) := by ring
    have e1 : (b ^ (-p))⁻¹ = b ^ p := by
      rw [Real.rpow_neg hb.le, inv_inv]
    have e2 : b ^ p * b ^ p * b ^ (-p') = b ^ (-(p' - 2 * p)) := by
      rw [← Real.rpow_add hb, ← Real.rpow_add hb]
      congr 1
      ring
    calc (C / c ^ 2) * b ^ (-(p' - 2 * p))
        = (C / c ^ 2) * (b ^ p * b ^ p * b ^ (-p')) := by rw [e2]
      _ = (C / c ^ 2) * ((b ^ (-p))⁻¹ ^ 2 * b ^ (-p')) := by rw [e1, pow_two]; ring
      _ = (c * b ^ (-p))⁻¹ ^ 2 * (C * b ^ (-p')) := by
          rw [mul_inv, mul_pow]
          field_simp
      _ = (1 - (1 - c * b ^ (-p)))⁻¹ ^ 2 * (C * b ^ (-p')) := by rw [h1]
  have hlim : Filter.Tendsto (fun b : ℝ => (C / c ^ 2) * b ^ (-(p' - 2 * p)))
      Filter.atTop (nhds 0) := by
    have h := (tendsto_const_nhds (x := C / c ^ 2)).mul
      (tendsto_rpow_neg_atTop (by linarith : (0 : ℝ) < p' - 2 * p))
    rwa [mul_zero] at h
  exact hlim.congr' key

/-! ## V5 TAIL SPINE (8/25, per Ben: "how much of the V5 tail estimate can go in Lean?")

The V5 rank-N repair (preflight #2 = analysis_ledger B10) decomposes as:
  (cited, NOT formalizable — Mathlib lacks operator ideals & manifold subellipticity):
    quantified hypoelliptic smoothing ⇒ singular-value power law s_i ≤ C·b^q·(i+1)^{−α},
    and Weyl majorization |λ_i| ≤ s_i. These two collapse into ONE quarantined
    hypothesis below: `hdom`.
  (PROVED here — the entire arithmetic downstream of the citation):
    v5_tail_le      — eigenvalue-power tails are summable and dominated by the
                      majorant's tails, for every truncation rank N;
    v5_tail_tendsto — the majorant's tails vanish as N → ∞ (the ε(N) → 0 of V5b);
    v5_rank_split   — THE THREE-TERM V5 STATEMENT the budget consumes: spectral-sum
                      drift ≤ (low-N drift, cited to stochastic stability [Drouot/DZ])
                      + tail(λ, N) + tail(μ, N). This is the "rerun b1_per_length with
                      three terms" architecture of the 8/15 V5 flag, machine-checked.
Power-law instantiation (t i = (i+1)^{−αℓ}, summable iff αℓ > 1 — p-series, citable to
Mathlib's `Real.summable_nat_rpow_inv`) and b-scaling (constants factor out of tsum by
`tsum_mul_left`) are one-line specializations left to the note's prose. -/

section V5Tail

/-- (V5b-i) Domination transfer: given the quarantined citation `hdom` (smoothing +
Weyl, packaged), the eigenvalue-power tails are summable and bounded by the majorant's
tails at every rank N. -/
theorem v5_tail_le (lam : ℕ → ℂ) (s : ℕ → ℝ) (ℓ : ℕ)
    (hdom : ∀ i, ‖lam i‖ ^ ℓ ≤ s i) (hs : Summable s) :
    Summable (fun i => ‖lam i‖ ^ ℓ) ∧
      ∀ N, (∑' i, ‖lam (i + N)‖ ^ ℓ) ≤ ∑' i, s (i + N) := by
  have hnn : ∀ i, 0 ≤ ‖lam i‖ ^ ℓ := fun i => pow_nonneg (norm_nonneg _) ℓ
  have hsum : Summable (fun i => ‖lam i‖ ^ ℓ) :=
    Summable.of_nonneg_of_le hnn hdom hs
  refine ⟨hsum, fun N => ?_⟩
  have h1 : Summable (fun i => ‖lam (i + N)‖ ^ ℓ) :=
    (summable_nat_add_iff N).2 hsum
  have h2 : Summable (fun i => s (i + N)) :=
    (summable_nat_add_iff N).2 hs
  exact h1.tsum_mono h2 fun i => hdom (i + N)

/-- (V5b-ii) The majorant's tails vanish: the ε(N) → 0 clause of the rank-N repair. -/
theorem v5_tail_tendsto (t : ℕ → ℝ) (ht : Summable t) :
    Filter.Tendsto (fun N => ∑' i, t (i + N)) Filter.atTop (nhds 0) := by
  have h1 : (fun N => ∑' i, t (i + N))
      = fun N => (∑' i, t i) - ∑ i ∈ Finset.range N, t i := by
    funext N
    have h := ht.sum_add_tsum_nat_add N
    linarith
  rw [h1]
  have h2 : Filter.Tendsto (fun N => ∑ i ∈ Finset.range N, t i)
      Filter.atTop (nhds (∑' i, t i)) := ht.hasSum.tendsto_sum_nat
  simpa using Filter.Tendsto.const_sub (∑' i, t i) h2

/-- (V5, assembled) THE THREE-TERM RANK-N STATEMENT: the drift between two spectral
power sums is at most the finite low-N drift (cited to stochastic stability) plus the
two tails (bounded via `v5_tail_le`, vanishing via `v5_tail_tendsto`). -/
theorem v5_rank_split (lam mu : ℕ → ℂ) (ℓ N : ℕ)
    (hl : Summable fun i => ‖lam i‖ ^ ℓ) (hm : Summable fun i => ‖mu i‖ ^ ℓ) :
    ‖(∑' i, lam i ^ ℓ) - ∑' i, mu i ^ ℓ‖ ≤
      (∑ i ∈ Finset.range N, ‖lam i ^ ℓ - mu i ^ ℓ‖)
        + (∑' i, ‖lam (i + N)‖ ^ ℓ) + ∑' i, ‖mu (i + N)‖ ^ ℓ := by
  have hlC : Summable fun i => lam i ^ ℓ :=
    Summable.of_norm (by simpa [norm_pow] using hl)
  have hmC : Summable fun i => mu i ^ ℓ :=
    Summable.of_norm (by simpa [norm_pow] using hm)
  have hlT : Summable fun i => lam (i + N) ^ ℓ := (summable_nat_add_iff N).2 hlC
  have hmT : Summable fun i => mu (i + N) ^ ℓ := (summable_nat_add_iff N).2 hmC
  have hsplitL := hlC.sum_add_tsum_nat_add N
  have hsplitM := hmC.sum_add_tsum_nat_add N
  have key : (∑' i, lam i ^ ℓ) - ∑' i, mu i ^ ℓ
      = (∑ i ∈ Finset.range N, (lam i ^ ℓ - mu i ^ ℓ))
        + ((∑' i, lam (i + N) ^ ℓ) - ∑' i, mu (i + N) ^ ℓ) := by
    rw [Finset.sum_sub_distrib, ← hsplitL, ← hsplitM]; ring
  calc ‖(∑' i, lam i ^ ℓ) - ∑' i, mu i ^ ℓ‖
      ≤ ‖∑ i ∈ Finset.range N, (lam i ^ ℓ - mu i ^ ℓ)‖
        + ‖(∑' i, lam (i + N) ^ ℓ) - ∑' i, mu (i + N) ^ ℓ‖ := by
        rw [key]; exact norm_add_le _ _
    _ ≤ (∑ i ∈ Finset.range N, ‖lam i ^ ℓ - mu i ^ ℓ‖)
        + (‖∑' i, lam (i + N) ^ ℓ‖ + ‖∑' i, mu (i + N) ^ ℓ‖) := by
        gcongr
        · exact norm_sum_le _ _
        · exact norm_sub_le _ _
    _ ≤ (∑ i ∈ Finset.range N, ‖lam i ^ ℓ - mu i ^ ℓ‖)
        + ((∑' i, ‖lam (i + N)‖ ^ ℓ) + ∑' i, ‖mu (i + N)‖ ^ ℓ) := by
        gcongr
        · calc ‖∑' i, lam (i + N) ^ ℓ‖ ≤ ∑' i, ‖lam (i + N) ^ ℓ‖ :=
                norm_tsum_le_tsum_norm (by simpa [norm_pow] using (summable_nat_add_iff N).2 hl)
            _ = ∑' i, ‖lam (i + N)‖ ^ ℓ := by simp [norm_pow]
        · calc ‖∑' i, mu (i + N) ^ ℓ‖ ≤ ∑' i, ‖mu (i + N) ^ ℓ‖ :=
                norm_tsum_le_tsum_norm (by simpa [norm_pow] using (summable_nat_add_iff N).2 hm)
            _ = ∑' i, ‖mu (i + N)‖ ^ ℓ := by simp [norm_pow]
    _ = _ := by ring

/-! ### The geometric-mean bridge (8/25, per Ben: "do the two lines in Lean so the
citation is just Weyl"). Weyl's inequality gives MAJORIZATION
(∏‖λᵢ‖ ≤ ∏ sᵢ), not pointwise domination. For a power-law majorant the pointwise
bound is recovered — constant inflated by e^α — via geometric means and the factorial
bound (m/e)^m ≤ m! (Mathlib's Stirling estimate). With `hdom_pow_of_weyl` below, the
instantiation of v5_tail_le's `hdom` cites ONLY: Weyl (multiplicative form, the
hypothesis `hweyl`) + the singular-value power law `hpow` (quantified smoothing). -/

/-- Factorial lower bound (m/e)^m ≤ m!, m ≥ 1, from Mathlib's Stirling estimate. -/
lemma pow_div_exp_le_factorial (m : ℕ) (hm : 1 ≤ m) :
    ((m : ℝ) / Real.exp 1) ^ m ≤ (m.factorial : ℝ) := by
  have h := Stirling.le_factorial_stirling m
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have h1 : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi * m) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    apply Real.sqrt_le_sqrt
    nlinarith [Real.pi_gt_three]
  calc ((m : ℝ) / Real.exp 1) ^ m
      = 1 * ((m : ℝ) / Real.exp 1) ^ m := (one_mul _).symm
    _ ≤ Real.sqrt (2 * Real.pi * m) * ((m : ℝ) / Real.exp 1) ^ m :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ ≤ (m.factorial : ℝ) := h

/-- ⚡WEYL ⇒ POINTWISE: from the multiplicative Weyl majorization (`hweyl` — the sole
operator-theory citation) and a power-law majorant (`hpow` — quantified smoothing),
the pointwise eigenvalue bound follows, constant inflated by e^α. Eigenvalues are
assumed ordered by modulus (`hanti`), as in Weyl's setup. -/
theorem hdom_of_weyl (lam : ℕ → ℂ) (s : ℕ → ℝ) (C α : ℝ)
    (hC : 0 ≤ C) (hα : 0 ≤ α)
    (hanti : Antitone fun i => ‖lam i‖)
    (hs0 : ∀ i, 0 ≤ s i)
    (hweyl : ∀ n : ℕ, (∏ i ∈ Finset.range (n + 1), ‖lam i‖)
        ≤ ∏ i ∈ Finset.range (n + 1), s i)
    (hpow : ∀ i, s i ≤ C * ((i : ℝ) + 1) ^ (-α)) :
    ∀ n : ℕ, ‖lam n‖ ≤ (C * Real.exp α) * ((n : ℝ) + 1) ^ (-α) := by
  intro n
  set m : ℕ := n + 1 with hmdef
  have hm1 : 1 ≤ m := Nat.le_add_left 1 n
  have hmR : (0 : ℝ) < (m : ℝ) := by positivity
  have hcast : ((n : ℝ) + 1) = (m : ℝ) := by push_cast [hmdef]; ring
  -- Step A: ‖λ_n‖^m ≤ ∏_{i<m} ‖λ_i‖ (ordering).
  have hA : ‖lam n‖ ^ m ≤ ∏ i ∈ Finset.range m, ‖lam i‖ := by
    have hle : ∀ i ∈ Finset.range m, ‖lam n‖ ≤ ‖lam i‖ := by
      intro i hi
      have hi' := Finset.mem_range.mp hi
      exact hanti (by omega)
    calc ‖lam n‖ ^ m = ∏ _i ∈ Finset.range m, ‖lam n‖ := by
          rw [Finset.prod_const, Finset.card_range]
      _ ≤ ∏ i ∈ Finset.range m, ‖lam i‖ :=
          Finset.prod_le_prod (fun _ _ => norm_nonneg _) hle
  -- Step B: ∏ s ≤ C^m · (m!)^{−α} (power law + factorial identity).
  have hfactpos : (0 : ℝ) < (m.factorial : ℝ) := by
    exact_mod_cast m.factorial_pos
  have hB : (∏ i ∈ Finset.range m, s i)
      ≤ C ^ m * ((m.factorial : ℝ)) ^ (-α) := by
    have h1 : (∏ i ∈ Finset.range m, s i)
        ≤ ∏ i ∈ Finset.range m, (C * ((i : ℝ) + 1) ^ (-α)) :=
      Finset.prod_le_prod (fun i _ => hs0 i) (fun i _ => hpow i)
    have h2 : ∏ i ∈ Finset.range m, (C * ((i : ℝ) + 1) ^ (-α))
        = C ^ m * ∏ i ∈ Finset.range m, ((i : ℝ) + 1) ^ (-α) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    have h3 : (∏ i ∈ Finset.range m, ((i : ℝ) + 1) ^ (-α))
        = (∏ i ∈ Finset.range m, ((i : ℝ) + 1)) ^ (-α) :=
      Real.finsetProd_rpow (Finset.range m) (fun i => ((i : ℝ) + 1))
        (fun i _ => by positivity) (-α)
    have h4 : (∏ i ∈ Finset.range m, ((i : ℝ) + 1)) = (m.factorial : ℝ) := by
      rw [← Finset.prod_range_add_one_eq_factorial m, Nat.cast_prod]
      push_cast
      rfl
    rw [h2, h3, h4] at h1
    exact h1
  -- Step C: combine A, Weyl, B.
  have hC1 : ‖lam n‖ ^ m ≤ C ^ m * ((m.factorial : ℝ)) ^ (-α) :=
    le_trans hA (le_trans (hweyl n) hB)
  -- Step D: (m!)^{−α} ≤ exp(αm) · m^{−αm} from the factorial bound.
  have hfact := pow_div_exp_le_factorial m hm1
  have hbasepos : (0 : ℝ) < ((m : ℝ) / Real.exp 1) ^ m := by positivity
  have hD : ((m.factorial : ℝ)) ^ (-α)
      ≤ Real.exp (α * m) * ((m : ℝ) ^ (-α)) ^ m := by
    have hX : (((m : ℝ) / Real.exp 1) ^ m) ^ (α : ℝ)
        ≤ ((m.factorial : ℝ)) ^ (α : ℝ) :=
      Real.rpow_le_rpow hbasepos.le hfact hα
    -- compute the left side via log-injectivity: ((m/e)^m)^α = m^{αm} · exp(αm)⁻¹
    have hLpos : (0 : ℝ) < (((m : ℝ) / Real.exp 1) ^ m) ^ (α : ℝ) :=
      Real.rpow_pos_of_pos hbasepos _
    have hRpos : (0 : ℝ) < ((m : ℝ) ^ (α : ℝ)) ^ m * (Real.exp (α * m))⁻¹ := by
      positivity
    have hY : (((m : ℝ) / Real.exp 1) ^ m) ^ (α : ℝ)
        = ((m : ℝ) ^ (α : ℝ)) ^ m * (Real.exp (α * m))⁻¹ := by
      rw [← Real.exp_log hLpos, ← Real.exp_log hRpos]
      congr 1
      rw [Real.log_rpow hbasepos, Real.log_pow,
        Real.log_div (ne_of_gt hmR) (Real.exp_pos 1).ne', Real.log_exp,
        Real.log_mul (by positivity : (0:ℝ) < ((m : ℝ) ^ (α : ℝ)) ^ m).ne'
          (by positivity : (0:ℝ) < (Real.exp (α * m))⁻¹).ne',
        Real.log_pow, Real.log_rpow hmR, Real.log_inv, Real.log_exp]
      ring
    rw [hY] at hX
    -- invert: (m!)^{−α} = ((m!)^α)⁻¹ ≤ (m^{αm} e^{−αm})⁻¹ = e^{αm} m^{−αm}
    have hZpos : (0 : ℝ) < ((m : ℝ) ^ (α : ℝ)) ^ m * (Real.exp (α * m))⁻¹ := hRpos
    have hinv : (((m.factorial : ℝ)) ^ (α : ℝ))⁻¹
        ≤ (((m : ℝ) ^ (α : ℝ)) ^ m * (Real.exp (α * m))⁻¹)⁻¹ := by
      rw [← one_div, ← one_div]
      exact one_div_le_one_div_of_le hZpos hX
    rw [Real.rpow_neg hfactpos.le]
    calc (((m.factorial : ℝ)) ^ (α : ℝ))⁻¹
        ≤ (((m : ℝ) ^ (α : ℝ)) ^ m * (Real.exp (α * m))⁻¹)⁻¹ := hinv
      _ = Real.exp (α * m) * (((m : ℝ) ^ (α : ℝ)) ^ m)⁻¹ := by
          rw [mul_inv, inv_inv, mul_comm]
      _ = Real.exp (α * m) * ((m : ℝ) ^ (-α)) ^ m := by
          congr 1
          rw [← inv_pow]
          congr 1
          rw [← Real.rpow_neg hmR.le]
  -- Step E: assemble the m-th power inequality, then take m-th roots.
  have hE : ‖lam n‖ ^ m ≤ ((C * Real.exp α) * ((m : ℝ) ^ (-α))) ^ m := by
    have hexp : (Real.exp α) ^ m = Real.exp (α * m) := by
      rw [← Real.exp_nat_mul, mul_comm]
    calc ‖lam n‖ ^ m
        ≤ C ^ m * ((m.factorial : ℝ)) ^ (-α) := hC1
      _ ≤ C ^ m * (Real.exp (α * m) * ((m : ℝ) ^ (-α)) ^ m) :=
          mul_le_mul_of_nonneg_left hD (by positivity)
      _ = ((C * Real.exp α) * ((m : ℝ) ^ (-α))) ^ m := by
          rw [mul_pow, mul_pow, hexp]; ring
  have hfinal : ‖lam n‖ ≤ (C * Real.exp α) * ((m : ℝ) ^ (-α)) := by
    have hmne : ((m : ℕ) : ℝ) ≠ 0 := ne_of_gt hmR
    have collapse : ∀ x : ℝ, 0 ≤ x → (x ^ m) ^ ((m : ℝ)⁻¹) = x := by
      intro x hx
      rw [← Real.rpow_natCast x m, ← Real.rpow_mul hx,
        mul_inv_cancel₀ hmne, Real.rpow_one]
    have h1 : (‖lam n‖ ^ m) ^ ((m : ℝ)⁻¹)
        ≤ (((C * Real.exp α) * ((m : ℝ) ^ (-α))) ^ m) ^ ((m : ℝ)⁻¹) :=
      Real.rpow_le_rpow (by positivity) hE (by positivity)
    rwa [collapse _ (norm_nonneg _), collapse _ (by positivity)] at h1
  rwa [hcast]

/-- The ℓ-power form feeding `v5_tail_le`: instantiates hdom with the explicit
power-law majorant, citing ONLY Weyl + the smoothing power law. -/
theorem hdom_pow_of_weyl (lam : ℕ → ℂ) (s : ℕ → ℝ) (C α : ℝ) (ℓ : ℕ)
    (hC : 0 ≤ C) (hα : 0 ≤ α)
    (hanti : Antitone fun i => ‖lam i‖)
    (hs0 : ∀ i, 0 ≤ s i)
    (hweyl : ∀ n : ℕ, (∏ i ∈ Finset.range (n + 1), ‖lam i‖)
        ≤ ∏ i ∈ Finset.range (n + 1), s i)
    (hpow : ∀ i, s i ≤ C * ((i : ℝ) + 1) ^ (-α)) :
    ∀ n : ℕ, ‖lam n‖ ^ ℓ
      ≤ ((C * Real.exp α) ^ ℓ) * ((n : ℝ) + 1) ^ (-α * (ℓ : ℝ)) := by
  intro n
  have h := hdom_of_weyl lam s C α hC hα hanti hs0 hweyl hpow n
  calc ‖lam n‖ ^ ℓ
      ≤ ((C * Real.exp α) * ((n : ℝ) + 1) ^ (-α)) ^ ℓ :=
        pow_le_pow_left₀ (norm_nonneg _) h ℓ
    _ = ((C * Real.exp α) ^ ℓ) * ((n : ℝ) + 1) ^ (-α * (ℓ : ℝ)) := by
        rw [mul_pow, ← Real.rpow_natCast (((n : ℝ) + 1) ^ (-α)) ℓ,
          ← Real.rpow_mul (by positivity)]

end V5Tail

/-! ## V5 FROM PARTS (8/28 pm, per Ben: "shouldn't the lean encompass all the
packaging so that the inputs remain hpt and whatever discharges the other half?")

The composite axiom V5 packages two different inputs behind one symbol (D =
finite-part drift [Drouot — `hpt`'s face] + tails [hdom]). This section makes the
packaging ITSELF machine-checked and BYPASSES the placeholder:
`b1_total_error_vanishes_ofPointwise` reaches B1's conclusion from the
citation-shaped inputs directly — ⚡its axiom audit must list V1–V4 (+ vehicle
constants) and NEITHER V5 NOR D. Hypothesis shapes match endpoints_8_20 §4:
  `hpt`   — per-resonance convergence (Drouot's citable form, twisted flag);
  `htail` — uniform tail smallness at fixed cuts (hdom at first-power grade);
  `hlam`/`hmu` — trace-class summability bookkeeping (V1/V2-grade facts). -/

/-- Tails of a summable nonnegative series are antitone in the cut. (Local copy of
endpoints_8_20's `tail_anti`: that file imports this one, so sharing would invert
the import.) -/
theorem tail_anti' (t : ℕ → ℝ) (h0 : ∀ i, 0 ≤ t i) (ht : Summable t)
    {N₁ N₂ : ℕ} (h : N₁ ≤ N₂) :
    (∑' i, t (i + N₂)) ≤ ∑' i, t (i + N₁) := by
  have hs : Summable fun i => t (i + N₁) := (summable_nat_add_iff N₁).2 ht
  have key := hs.sum_add_tsum_nat_add (N₂ - N₁)
  have hidx : (fun i => t (i + (N₂ - N₁) + N₁)) = fun i => t (i + N₂) := by
    funext i; congr 1; omega
  rw [hidx] at key
  have hnn : 0 ≤ ∑ i ∈ Finset.range (N₂ - N₁), t (i + N₁) :=
    Finset.sum_nonneg fun i _ => h0 _
  linarith

/-- THE PACKAGING, machine-checked (zero axioms): the ℓ¹ drift between two spectra
splits at any cut N into finite-part drift plus the two tails — what the composite
D of axiom V5 decomposes into on instantiation. -/
theorem drift_of_parts (x y : ℕ → ℂ) (N : ℕ)
    (hx : Summable fun i => ‖x (i + N)‖) (hy : Summable fun i => ‖y (i + N)‖) :
    Summable (fun i => ‖x i - y i‖) ∧
      (∑' i, ‖x i - y i‖) ≤ (∑ i ∈ Finset.range N, ‖x i - y i‖)
        + ((∑' i, ‖x (i + N)‖) + ∑' i, ‖y (i + N)‖) := by
  have htails : Summable fun i => ‖x (i + N) - y (i + N)‖ :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _)
      (fun i => norm_sub_le _ _) (hx.add hy)
  have hsum : Summable fun i => ‖x i - y i‖ := (summable_nat_add_iff N).1 htails
  refine ⟨hsum, ?_⟩
  have hsplit := hsum.sum_add_tsum_nat_add N
  have htb : (∑' i, ‖x (i + N) - y (i + N)‖)
      ≤ (∑' i, ‖x (i + N)‖) + ∑' i, ‖y (i + N)‖ := by
    calc (∑' i, ‖x (i + N) - y (i + N)‖)
        ≤ ∑' i, (‖x (i + N)‖ + ‖y (i + N)‖) :=
          Summable.tsum_le_tsum (fun i => norm_sub_le _ _) htails (hx.add hy)
      _ = (∑' i, ‖x (i + N)‖) + ∑' i, ‖y (i + N)‖ :=
          (hx.hasSum.add hy.hasSum).tsum_eq
  linarith

/-- `b1_per_length` with the drift budget as a HYPOTHESIS instead of axiom V5. -/
theorem b1_per_length_ofDrift (b : ℝ) (hb : b₀ ≤ b) (n : ℕ) (Dv : ℝ)
    (hs : Summable fun i => ‖kineticRes b i - endpointRes i‖)
    (hbound : (∑' i, ‖kineticRes b i - endpointRes i‖) ≤ Dv) :
    ‖heatTrace b (n + 1) - orbitSum (n + 1)‖ ≤ (n + 1) * θ ^ n * Dv := by
  obtain ⟨V3k, V3e⟩ := V3
  obtain ⟨V4k, V4e⟩ := V4
  have hθ0 : 0 ≤ θ := hθ.1
  set f : ℕ → ℂ := fun i => kineticRes b i ^ (n + 1) - endpointRes i ^ (n + 1) with hf
  have hsub : HasSum f (heatTrace b (n + 1) - orbitSum (n + 1)) :=
    (V1 b hb n).sub (V2 n)
  have hterm : ∀ i : ℕ, ‖f i‖
      ≤ ((n : ℝ) + 1) * θ ^ n * ‖kineticRes b i - endpointRes i‖ := by
    intro i
    match i with
    | 0 =>
        simp [hf, V3k b hb, V3e]
    | (i + 1) =>
        exact pow_succ_sub_bound _ _ θ (V4k b hb i) (V4e i) n
  have hbnd : Summable (fun i =>
      ((n : ℝ) + 1) * θ ^ n * ‖kineticRes b i - endpointRes i‖) :=
    hs.mul_left _
  have hnorm : Summable (fun i => ‖f i‖) :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) hterm hbnd
  have hc : (0 : ℝ) ≤ ((n : ℝ) + 1) * θ ^ n :=
    mul_nonneg (by positivity) (pow_nonneg hθ0 n)
  have h1 : ‖heatTrace b (n + 1) - orbitSum (n + 1)‖ ≤ ∑' i, ‖f i‖ := by
    rw [← hsub.tsum_eq]
    exact norm_tsum_le_tsum_norm hnorm
  have h3 : (∑' i, ‖f i‖) ≤ ((n : ℝ) + 1) * θ ^ n * Dv := by
    calc (∑' i, ‖f i‖)
        ≤ ∑' i, ((n : ℝ) + 1) * θ ^ n * ‖kineticRes b i - endpointRes i‖ :=
          Summable.tsum_le_tsum hterm hnorm hbnd
      _ = ((n : ℝ) + 1) * θ ^ n * ∑' i, ‖kineticRes b i - endpointRes i‖ :=
          tsum_mul_left
      _ ≤ ((n : ℝ) + 1) * θ ^ n * Dv := mul_le_mul_of_nonneg_left hbound hc
  calc ‖heatTrace b (n + 1) - orbitSum (n + 1)‖
      ≤ ∑' i, ‖f i‖ := h1
    _ ≤ ((n : ℝ) + 1) * θ ^ n * Dv := h3
    _ = (n + 1) * θ ^ n * Dv := by ring

/-- `b1_aggregate` with the drift budget as a HYPOTHESIS instead of axiom V5. -/
theorem b1_aggregate_ofDrift (b : ℝ) (hb : b₀ ≤ b) (Dv : ℝ) (hDv : 0 ≤ Dv)
    (hs : Summable fun i => ‖kineticRes b i - endpointRes i‖)
    (hbound : (∑' i, ‖kineticRes b i - endpointRes i‖) ≤ Dv) (L : ℕ) :
    ∑ n ∈ Finset.range L, ‖heatTrace b (n + 1) - orbitSum (n + 1)‖
      ≤ (1 - θ)⁻¹ ^ 2 * Dv := by
  have hstep : ∀ n ∈ Finset.range L,
      ‖heatTrace b (n + 1) - orbitSum (n + 1)‖ ≤ ((n + 1 : ℝ) * θ ^ n) * Dv := by
    intro n _
    have := b1_per_length_ofDrift b hb n Dv hs hbound
    calc ‖heatTrace b (n + 1) - orbitSum (n + 1)‖
        ≤ (n + 1) * θ ^ n * Dv := this
      _ = ((n + 1 : ℝ) * θ ^ n) * Dv := by ring
  calc ∑ n ∈ Finset.range L, ‖heatTrace b (n + 1) - orbitSum (n + 1)‖
      ≤ ∑ n ∈ Finset.range L, ((n + 1 : ℝ) * θ ^ n) * Dv :=
        Finset.sum_le_sum hstep
    _ = (∑ n ∈ Finset.range L, ((n + 1 : ℝ) * θ ^ n)) * Dv := by
        rw [← Finset.sum_mul]
    _ ≤ (1 - θ)⁻¹ ^ 2 * Dv :=
        mul_le_mul_of_nonneg_right (sum_succ_mul_geometric_le hθ.1 hθ.2 L) hDv

/-- Finite-part drift vanishes: a FIXED finite sum of per-resonance convergences
(factored out of `b1_total_error_vanishes_ofPointwise` so each declaration stays
within the default elaboration budget). -/
theorem finite_drift_tendsto
    (hpt : ∀ i, Filter.Tendsto (fun b => kineticRes b i) Filter.atTop
      (nhds (endpointRes i))) (N : ℕ) :
    Filter.Tendsto (fun b => ∑ i ∈ Finset.range N, ‖kineticRes b i - endpointRes i‖)
      Filter.atTop (nhds 0) := by
  have h := tendsto_finsetSum (Finset.range N)
    (f := fun i b => ‖kineticRes b i - endpointRes i‖) (a := fun _ => (0 : ℝ))
    (fun i _ => by
      have h2 : Filter.Tendsto (fun b => kineticRes b i - endpointRes i)
          Filter.atTop (nhds 0) := by
        have := (hpt i).sub (tendsto_const_nhds (x := endpointRes i))
        rwa [sub_self] at this
      simpa using h2.norm)
  simpa using h

/-- ε-step of `b1_total_error_vanishes_ofPointwise`, factored so each declaration
stays within the default elaboration budget: from the three quarter-bounds at one b,
the windowed aggregate is < ε, for every window length. -/
theorem b1_eps_step (b : ℝ) (hb : b₀ ≤ b) (ε C : ℝ) (hε : 0 < ε) (hC0 : 0 < C)
    (hCne : C ≠ 0) (hCge : (1 - θ)⁻¹ ^ 2 ≤ C) (N : ℕ)
    (hsb : Summable fun i => ‖kineticRes b i‖)
    (hmu : Summable fun i => ‖endpointRes i‖)
    (h1 : (∑ i ∈ Finset.range N, ‖kineticRes b i - endpointRes i‖) < ε / (4 * C))
    (hlamN : (∑' i, ‖kineticRes b (i + N)‖) ≤ ε / (4 * C))
    (hmuN : (∑' i, ‖endpointRes (i + N)‖) ≤ ε / (4 * C)) (L : ℕ) :
    (∑ n ∈ Finset.range L, ‖heatTrace b (n + 1) - orbitSum (n + 1)‖) < ε := by
  have hxs : Summable fun i => ‖kineticRes b (i + N)‖ := (summable_nat_add_iff N).2 hsb
  have hys : Summable fun i => ‖endpointRes (i + N)‖ := (summable_nat_add_iff N).2 hmu
  obtain ⟨hs, hbound⟩ := drift_of_parts (kineticRes b) endpointRes N hxs hys
  have hDv : (∑' i, ‖kineticRes b i - endpointRes i‖) ≤ 3 * (ε / (4 * C)) := by
    linarith
  have hDv0 : (0 : ℝ) ≤ 3 * (ε / (4 * C)) := by
    have : (0 : ℝ) < ε / (4 * C) := div_pos hε (by linarith)
    linarith
  have hagg := b1_aggregate_ofDrift b hb (3 * (ε / (4 * C))) hDv0 hs hDv L
  calc (∑ n ∈ Finset.range L, ‖heatTrace b (n + 1) - orbitSum (n + 1)‖)
      ≤ (1 - θ)⁻¹ ^ 2 * (3 * (ε / (4 * C))) := hagg
    _ ≤ C * (3 * (ε / (4 * C))) :=
        mul_le_mul_of_nonneg_right hCge (by positivity)
    _ = 3 * ε / 4 := by
        rw [← mul_div_assoc, mul_comm 4 C, ← div_div, ← mul_div_assoc,
          ← mul_div_assoc, mul_div_cancel_left₀ _ hCne]
    _ < ε := by linarith

/-- B1's CONCLUSION FROM THE CITATION-SHAPED INPUTS DIRECTLY — V5 and D bypassed.
⚡AUDIT CRITERION: `#print axioms` must list V1–V4 + vehicle constants and NEITHER
V5 NOR D. The two substantive hypotheses are the SAME pair as leg 5b
(endpoints_8_20 §4): `hpt` = Drouot per-resonance convergence (twisted flag);
`htail` = hdom's tail control at first-power grade. `hlam`/`hmu` are V1/V2-grade
trace-class bookkeeping. (8/31: proof works against an opaque local constant C so
the default elaboration budget suffices — no `set_option maxHeartbeats`.) -/
theorem b1_total_error_vanishes_ofPointwise
    (hpt : ∀ i, Filter.Tendsto (fun b => kineticRes b i) Filter.atTop
      (nhds (endpointRes i)))
    (htail : ∀ ε > 0, ∃ N₀ : ℕ, ∀ᶠ b in Filter.atTop,
      (∑' i, ‖kineticRes b (i + N₀)‖) ≤ ε)
    (hlam : ∀ᶠ b in Filter.atTop, Summable fun i => ‖kineticRes b i‖)
    (hmu : Summable fun i => ‖endpointRes i‖) :
    ∀ ε > 0, ∀ᶠ b in Filter.atTop, ∀ L : ℕ,
      (∑ n ∈ Finset.range L, ‖heatTrace b (n + 1) - orbitSum (n + 1)‖) < ε := by
  intro ε hε
  obtain ⟨C, hC0, hCge⟩ : ∃ C : ℝ, 0 < C ∧ (1 - θ)⁻¹ ^ 2 ≤ C :=
    ⟨(1 - θ)⁻¹ ^ 2 + 1, by positivity, le_add_of_nonneg_right zero_le_one⟩
  have hCne : C ≠ 0 := ne_of_gt hC0
  have hquarter : (0 : ℝ) < ε / (4 * C) := div_pos hε (by linarith)
  obtain ⟨N₁, hN₁⟩ := htail _ hquarter
  obtain ⟨N₂, hN₂⟩ := ((v5_tail_tendsto (fun i => ‖endpointRes i‖) hmu).eventually
    (gt_mem_nhds hquarter)).exists
  set N := max N₁ N₂ with hNdef
  have hfin := finite_drift_tendsto hpt N
  have hev1 : ∀ᶠ b in Filter.atTop,
      (∑ i ∈ Finset.range N, ‖kineticRes b i - endpointRes i‖) < ε / (4 * C) :=
    hfin.eventually (gt_mem_nhds hquarter)
  have hmuN : (∑' i, ‖endpointRes (i + N)‖) ≤ ε / (4 * C) :=
    le_trans (tail_anti' _ (fun i => norm_nonneg _) hmu (le_max_right _ _))
      (le_of_lt hN₂)
  filter_upwards [hev1, hN₁, hlam, Filter.eventually_ge_atTop b₀] with b h1 h2 hsb hb
  intro L
  have hlamN : (∑' i, ‖kineticRes b (i + N)‖) ≤ ε / (4 * C) :=
    le_trans (tail_anti' _ (fun i => norm_nonneg _) hsb (le_max_left _ _)) h2
  exact b1_eps_step b hb ε C hε hC0 hCne hCge N hsb hmu h1 hlamN hmuN L

end FriedB1Spectral
