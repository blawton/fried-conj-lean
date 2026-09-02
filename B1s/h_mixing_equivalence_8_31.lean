/-
H ⟺ TWISTED ENDPOINT MIXING — THE STAGE-1 SKELETON (8/31, per Ben: separate file
from the H ⇒ Fried suite; plan on Front Page ¶4; routes: h_proof_routes_synthesis_8_31,
stage-2 literature: stage2_mixing_literature_8_31).

House method, one level up: quarantine the analytic estimates as named,
citation-shaped HYPOTHESES; machine-check everything downstream. ⚡AUDIT CRITERION:
this file has ZERO axioms of its own — `#print axioms` on every theorem must list
only Lean built-ins (unlike b1_spectral's vehicle block; here every input is an
explicit argument).

What is proved here (the assembly of stage 1):
  block_telescope / uniform_gap_of_block_mixing
      — THE TELESCOPE: a one-block twisted propagator with (i) poly(b) burn-in cost
        [`hburn` — hypoelliptic calibration, hdom-grade smoothing citation] and
        (ii) a b-UNIFORM per-m₀-block contraction [`hmix` — THE substantive input:
        endpoint twisted mixing transferred to one kinetic block by the
        shadowing/Wilson-line lemma (stage 1) — holonomy is homotopy-quantized, so
        the transfer is exact off an e^{−cb} event] yields H's shape
        ‖T_b^n‖ ≤ q^{n/m₀}·C·b^K. The mandatory b^K prefactor is exactly the
        burn-in cost — the machine-checked impossibility theorem's shape.
  pow_eq_exp_log / nat_div_cast_gt
      — the geometric-to-exponential bookkeeping (β = log q⁻¹ / m₀), split into two
        robust pieces the note's prose composes.
  midpoint_strict_contraction / opNorm_avg_lt_one
      — WHERE ACYCLICITY IS SPENT (the Itô–Kawada mechanism): two unitary holonomy
        readouts that disagree average to a strict contraction (parallelogram law);
        in finite dimension, no common vector ⇒ operator norm of the average < 1.
        Stated for two readouts — the general adapted-measure form is the same
        argument summed.
  dissipation_identity
      — route 5's banked identity: for L = T + c·S with Re⟪v,Tv⟫ = 0 (skew
        transport) and eigenvector v, Re λ·‖v‖² = c·Re⟪v,Sv⟫ — H's spectral half is
        a vertical-energy lower bound; no eigenvalue condition number appears.

What is NOT here and never will be (the quarantine): the shadowing/coupling
probabilistic core (SDEs on manifolds — beyond Mathlib), and stage 2 itself
(twisted Dolgopyat / anisotropic transfer operators — no hyperbolic-dynamics
library exists). Those enter ONLY through `hmix`.
-/
import Mathlib

set_option linter.style.header false

namespace FriedHMixing

open scoped ComplexInnerProductSpace

/-! ### §1 The block telescope (stage-1 assembly) -/

/-- THE TELESCOPE. If a one-block propagator `T` has burn-in bound `M` on partial
blocks and contracts by `q` over a full `m₀`-block, then `‖T^n‖ ≤ q^{n/m₀}·M`.
`hcon` is where the mixing input lands; `hburn` is the calibration cost. -/
theorem block_telescope {A : Type*} [NormedRing A] (T : A) {m₀ : ℕ} (hm₀ : 0 < m₀)
    {M q : ℝ}
    (hburn : ∀ r < m₀, ‖T ^ r‖ ≤ M)
    (hcon : ‖T ^ m₀‖ ≤ q) (n : ℕ) :
    ‖T ^ n‖ ≤ q ^ (n / m₀) * M := by
  have hr : n % m₀ < m₀ := Nat.mod_lt _ hm₀
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hburn (n % m₀) hr)
  by_cases hk : n / m₀ = 0
  · have h1 := Nat.div_add_mod n m₀
    rw [hk, Nat.mul_zero, Nat.zero_add] at h1
    have hn : n < m₀ := by rw [← h1]; exact hr
    calc ‖T ^ n‖ ≤ M := hburn n hn
      _ = q ^ (n / m₀) * M := by rw [hk, pow_zero, one_mul]
  · have hsplit : T ^ n = (T ^ m₀) ^ (n / m₀) * T ^ (n % m₀) := by
      conv_lhs => rw [← Nat.div_add_mod n m₀]
      rw [pow_add, pow_mul]
    rw [hsplit]
    calc ‖(T ^ m₀) ^ (n / m₀) * T ^ (n % m₀)‖
        ≤ ‖(T ^ m₀) ^ (n / m₀)‖ * ‖T ^ (n % m₀)‖ := norm_mul_le _ _
      _ ≤ ‖T ^ m₀‖ ^ (n / m₀) * M :=
          mul_le_mul (norm_pow_le' _ (Nat.pos_of_ne_zero hk)) (hburn _ hr)
            (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)
      _ ≤ q ^ (n / m₀) * M :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hcon _) hM0

/-- STAGE 1, ASSEMBLED: H's shape from the two citation-shaped inputs.
`hburn` = hypoelliptic calibration (poly(b) burn-in — the mandatory prefactor);
`hmix`  = THE substantive input: b-uniform contraction of one full block,
supplied by [endpoint twisted mixing] + [the shadowing/Wilson-line transfer].
Conclusion: ‖T_b^n‖ ≤ q^{n/m₀}·C·b^K for all b ≥ b₁ — H at block-sampled times. -/
theorem uniform_gap_of_block_mixing {A : Type*} [NormedRing A]
    (T : ℝ → A) {m₀ : ℕ} (hm₀ : 0 < m₀) (b₁ C K q : ℝ)
    (hburn : ∀ b ≥ b₁, ∀ r < m₀, ‖T b ^ r‖ ≤ C * b ^ K)
    (hmix : ∀ b ≥ b₁, ‖T b ^ m₀‖ ≤ q) :
    ∀ b ≥ b₁, ∀ n, ‖T b ^ n‖ ≤ q ^ (n / m₀) * (C * b ^ K) :=
  fun b hb n => block_telescope (T b) hm₀ (hburn b hb) (hmix b hb) n

/-- Geometric-to-exponential bookkeeping, piece 1: `q^k = e^{k·log q}`. -/
theorem pow_eq_exp_log {q : ℝ} (hq : 0 < q) (k : ℕ) :
    q ^ k = Real.exp ((k : ℝ) * Real.log q) := by
  rw [← Real.rpow_natCast q k, Real.rpow_def_of_pos hq, mul_comm]

/-- Geometric-to-exponential bookkeeping, piece 2: `⌊n/m₀⌋ > n/m₀ − 1`, so the
block-counted rate loses at most one block (a factor q⁻¹) against the continuous
rate β = log q⁻¹ / m₀. -/
theorem nat_div_cast_gt {n m₀ : ℕ} (hm₀ : 0 < m₀) :
    (n : ℝ) / (m₀ : ℝ) - 1 < ((n / m₀ : ℕ) : ℝ) := by
  have h2 := Nat.mod_lt n hm₀
  have h : n < (n / m₀ + 1) * m₀ := by
    calc n = m₀ * (n / m₀) + n % m₀ := (Nat.div_add_mod n m₀).symm
      _ < m₀ * (n / m₀) + m₀ := Nat.add_lt_add_left h2 _
      _ = (n / m₀ + 1) * m₀ := by ring
  have hm : (0 : ℝ) < (m₀ : ℝ) := by exact_mod_cast hm₀
  rw [sub_lt_iff_lt_add, div_lt_iff₀ hm]
  exact_mod_cast h

/-! ### §2 Where acyclicity is spent (the Itô–Kawada mechanism) -/

/-- Two unit-length holonomy readouts that DISAGREE average to a strict
contraction — pure parallelogram law. `x = U v`, `y = V v` in the application. -/
theorem midpoint_strict_contraction {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {x y : E} {c : ℝ}
    (hx : ‖x‖ = c) (hy : ‖y‖ = c) (hne : x ≠ y) :
    ‖x + y‖ < 2 * c := by
  have hpar := parallelogram_law_with_norm (𝕜 := ℂ) x y
  rw [hx, hy] at hpar
  have hxy : 0 < ‖x - y‖ := by
    rw [norm_pos_iff, sub_ne_zero]; exact hne
  have hc : 0 ≤ c := hx ▸ norm_nonneg x
  nlinarith [norm_nonneg (x + y), hc, mul_pos hxy hxy, hpar,
    sq_nonneg (‖x + y‖ - 2 * c), sq_nonneg (‖x + y‖ + 2 * c)]

/-- ACYCLICITY SPENT, operator form (finite dimension): two norm-preserving
operators with NO common vector — the shape acyclicity delivers for holonomy
readouts of an acyclic unitary rep — have averaged operator norm < 1. The general
adapted-measure Itô–Kawada statement is this argument summed over the support. -/
theorem opNorm_avg_lt_one {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [Nontrivial E]
    (U V : E →L[ℂ] E) (hU : ∀ w, ‖U w‖ = ‖w‖) (hV : ∀ w, ‖V w‖ = ‖w‖)
    (hne : ∀ w, w ≠ 0 → U w ≠ V w) :
    ‖(2 : ℝ)⁻¹ • (U + V)‖ < 1 := by
  set A := (2 : ℝ)⁻¹ • (U + V) with hA
  obtain ⟨x₀, hx₀s, hmax⟩ := (isCompact_sphere (0 : E) 1).exists_isMaxOn
    (nonempty_subtype.mp (NormedSpace.sphere_nonempty_rclike (𝕜 := ℂ) zero_le_one))
    (Continuous.continuousOn (continuous_norm.comp A.continuous))
  have hx₀ : ‖x₀‖ = 1 := by simpa [mem_sphere_zero_iff_norm] using hx₀s
  have hbound : ∀ w, ‖A w‖ ≤ ‖A x₀‖ * ‖w‖ := by
    intro w
    rcases eq_or_ne w 0 with rfl | hw
    · simp
    · have hw' : ‖w‖ ≠ 0 := norm_ne_zero_iff.2 hw
      have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw
      have hmem : ‖w‖⁻¹ • w ∈ Metric.sphere (0 : E) 1 := by
        simp [norm_smul, inv_mul_cancel₀ hw']
      have hle := hmax hmem
      have hle' : ‖w‖⁻¹ * ‖A w‖ ≤ ‖A x₀‖ := by
        have h0 : A (‖w‖⁻¹ • w) = ‖w‖⁻¹ • A w := A.map_smul_of_tower _ _
        simpa [Function.comp_apply, h0, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (inv_nonneg.mpr (norm_nonneg w))] using hle
      have := mul_le_mul_of_nonneg_left hle' (norm_nonneg w)
      rw [mul_inv_cancel_left₀ hw'] at this
      calc ‖A w‖ ≤ ‖w‖ * ‖A x₀‖ := by
            simpa [Function.comp_apply] using this
        _ = ‖A x₀‖ * ‖w‖ := mul_comm _ _
  have hx₀ne : x₀ ≠ 0 := by
    intro h; rw [h, norm_zero] at hx₀; norm_num at hx₀
  have hAx₀ : ‖A x₀‖ < 1 := by
    have h1 : ‖U x₀‖ = 1 := by rw [hU, hx₀]
    have h2 : ‖V x₀‖ = 1 := by rw [hV, hx₀]
    have h4 : ‖U x₀ + V x₀‖ < 2 * 1 :=
      midpoint_strict_contraction h1 h2 (hne x₀ hx₀ne)
    have hAval : A x₀ = (2 : ℝ)⁻¹ • (U x₀ + V x₀) := by
      simp [hA, add_apply]
    rw [hAval, norm_smul, Real.norm_eq_abs]
    have habs : |(2 : ℝ)⁻¹| = 2⁻¹ := by norm_num
    rw [habs]
    linarith
  calc ‖A‖ ≤ ‖A x₀‖ := A.opNorm_le_bound (norm_nonneg _) hbound
    _ < 1 := hAx₀

/-! ### §3 The dissipation identity (route 5, banked) -/

/-- ROUTE 5's IDENTITY: for `L = T + c·S` with skew transport part
(`Re⟪v, Tv⟫ = 0`) and an eigenvector `v`, the eigenvalue's real part is the scaled
dissipation quadratic form — H's spectral half is a vertical-energy lower bound,
with NO eigenvalue condition number anywhere. -/
theorem dissipation_identity {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    (T S : E →L[ℂ] E) (c : ℝ) (lam : ℂ) (v : E)
    (heig : T v + (c : ℂ) • S v = lam • v)
    (hskew : (⟪v, T v⟫).re = 0) :
    lam.re * ‖v‖ ^ 2 = c * (⟪v, S v⟫).re := by
  have h := congrArg (fun w => (⟪v, w⟫ : ℂ)) heig
  simp only [inner_add_right, inner_smul_right] at h
  have hvv : (⟪v, v⟫ : ℂ) = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [hvv] at h
  have hre := congrArg Complex.re h
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, zero_mul] at hre
  linarith [hre, hskew]


/-! ### §4 The arithmetic-resonance endgame (8/31, per Ben "try this" —
stage-2 rigidity sketch: stage2_rigidity_sketch_8_31.md)

The R1 case of the rigidity lemma ends with: the accessibility-cycle constraint
forces a·t_c ∈ 2πℤ for a nondegenerate interval of time defects t_c (contact
non-integrability), hence a = 0. That endgame is pure real analysis: -/

/-- PHASE RIGIDITY (R1's endgame): a frequency whose phase is trivial on all small
times is zero. Consumed with: contact non-integrability supplies the interval of
accessibility-cycle time defects on which the twisted-eigenfunction constraint
forces `a * t ∈ 2πℤ`. -/
theorem freq_eq_zero_of_discrete_phase (a : ℝ) {ε : ℝ} (hε : 0 < ε)
    (h : ∀ t : ℝ, |t| < ε → ∃ n : ℤ, a * t = 2 * Real.pi * n) : a = 0 := by
  by_contra ha
  have hapos : 0 < |a| := abs_pos.mpr ha
  set t := min (ε / 2) (Real.pi / |a|) with ht
  have htpos : 0 < t := lt_min (by linarith) (div_pos Real.pi_pos hapos)
  have htε : |t| < ε := by
    rw [abs_of_pos htpos]
    calc t ≤ ε / 2 := min_le_left _ _
      _ < ε := by linarith
  obtain ⟨n, hn⟩ := h t htε
  have hbound : |a * t| ≤ Real.pi := by
    rw [abs_mul, abs_of_pos htpos]
    calc |a| * t ≤ |a| * (Real.pi / |a|) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) (abs_nonneg a)
      _ = Real.pi := by field_simp
  have hn0 : n = 0 := by
    by_contra hn0
    have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      have := Int.one_le_abs (by exact_mod_cast hn0 : n ≠ 0)
      exact_mod_cast this
    have h2 : 2 * Real.pi ≤ |a * t| := by
      rw [hn, abs_mul, abs_mul]
      have hpi : |(2 : ℝ)| * |Real.pi| = 2 * Real.pi := by
        rw [abs_of_pos (by norm_num : (0:ℝ) < 2), abs_of_pos Real.pi_pos]
      calc 2 * Real.pi = 2 * Real.pi * 1 := by ring
        _ ≤ 2 * Real.pi * |(n : ℝ)| := by
            have : (0:ℝ) ≤ 2 * Real.pi := by positivity
            exact mul_le_mul_of_nonneg_left h1 this
        _ = |(2 : ℝ)| * |Real.pi| * |(n : ℝ)| := by rw [hpi]
    linarith [Real.pi_pos]
  rw [hn0] at hn
  simp at hn
  rcases hn with h | h
  · exact ha h
  · exact absurd h (ne_of_gt htpos)

end FriedHMixing
