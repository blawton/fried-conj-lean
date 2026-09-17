/-
FROM CDDP (4.22) TO THE CLUSTER DATA — bottoming the rate ledger out in displayed equations (9/08).

Companion to `fried_crossing_rate_9_07` (same leg). That file consumes the twin's rate from
the cluster data a = tr N, b = det N with the two numbers a(0,0) = r₀ > 0, b(0,0) = 0 taken as
hypotheses `ha0`, `hb0`, and takes a, b themselves as given functions. This file derives both
from what CDDP actually display, in two finite-dimensional steps.

§1 FirstVariation — CDDP (4.22) in the basis (c, ψ) of Res¹₀: the first-variation matrix P of
∂_τZ(0) in the pairing B(u,u*) = ∫α∧dα∧u∧u* has VANISHING c-row and c-column (dc = 0), so
P = !![0,0;0,p] with p = the (4.22) pairing of the non-closed state. The pairing-relative
matrix N (the matrix of ∂_τZ(0) as an endomorphism) is the unique solution of B·N = P; it is
written explicitly (`Nmat`), and: det N = 0, tr N = B_cc·p/det B — the main note's
r₀ = −S·B_cc/det B — so the eigenvalues are exactly {0, B_cc·p/det B} (`charpoly_roots`):
the closed state is frozen, the non-closed state moves with rate tr N, and that rate is
non-zero iff p ≠ 0, which is CDDP's non-degeneracy (1.3). With CDDP (3.55)–(3.56) (B block
diagonal) the rate is p/B_ψψ. Over ℝ this feeds `TwinRate.wPlus` directly.

§2 Hadamard — the divisibility step. If the cluster matrix M(θ,τ) is C¹ in τ entrywise with
M(θ,0) = s*(θ)·1 (hdouble's semisimplicity, `Saturation`) and ∂_τM is jointly continuous at
(0,0), then N(θ,τ) := (M(θ,τ) − s*(θ)·1)/τ, extended by ∂_τM(θ,0) at τ = 0, is jointly
continuous at (0,0) (mean value theorem entrywise), M = s*·1 + τ·N identically, and the
characteristic polynomial of M is z² − clusterTrace·z + clusterDet with a = tr N, b = det N —
so `TwinRate.cluster_roots` applies to the ACTUAL cluster matrix. a, b are jointly continuous
at (0,0) with a(0,0) = tr ∂_τM(0,0), b(0,0) = det ∂_τM(0,0), i.e. the numbers of §1.

§3 Capstone wrapper — `fried_fails_at_crossing_of_cddp_inputs`: the cluster capstone with
[9/16: the §3 capstone `fried_fails_at_crossing_of_cddp_inputs` was REMOVED for the Palomar entry as superseded;
§1–§2 remain and are used by `fried_counterexample_of_resolvent_inputs`.]
`ha0`, `hb0` REPLACED by "∂_τM(0,0) is the (4.22) matrix" (B, p as in §1, orientation
B_cc·p/det B > 0). What remains hypothesis-shaped about regularity: a, b differentiable in τ
with derivatives jointly continuous at (0,0) (one more derivative of M than §2 proves).

⚡AUDIT CRITERION: ZERO axioms of its own — `#print axioms` on every theorem = built-ins only.
-/
import B1s.fried_crossing_rate_9_07

set_option linter.style.header false

namespace FriedCrossing

open Filter Topology Matrix

/-! ## §1 CDDP (4.22) as 2×2 algebra -/
namespace FirstVariation

variable {K : Type*} [Field K]

/-- The numerator matrix of N = B⁻¹P: adjugate(B)·P. -/
def Nmat0 (Bcc Bcψ p : K) : Matrix (Fin 2) (Fin 2) K := !![0, -(Bcψ * p); 0, Bcc * p]

/-- The pairing-relative first-variation matrix N = B⁻¹P = (det B)⁻¹·adjugate(B)·P, explicitly. -/
def Nmat (Bcc Bcψ Bψc Bψψ p : K) : Matrix (Fin 2) (Fin 2) K :=
  (1 / (Bcc * Bψψ - Bcψ * Bψc)) • Nmat0 Bcc Bcψ p

theorem det_Bmat (Bcc Bcψ Bψc Bψψ : K) :
    (Bmat Bcc Bcψ Bψc Bψψ).det = Bcc * Bψψ - Bcψ * Bψc := by
  simp [Bmat, Matrix.det_fin_two]

theorem Bmat_mul_Nmat0 (Bcc Bcψ Bψc Bψψ p : K) :
    Bmat Bcc Bcψ Bψc Bψψ * Nmat0 Bcc Bcψ p = (Bcc * Bψψ - Bcψ * Bψc) • Pmat p := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Bmat, Nmat0, Pmat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem Bmat_mul_Nmat {Bcc Bcψ Bψc Bψψ p : K} (h : Bcc * Bψψ - Bcψ * Bψc ≠ 0) :
    Bmat Bcc Bcψ Bψc Bψψ * Nmat Bcc Bcψ Bψc Bψψ p = Pmat p := by
  rw [Nmat, Matrix.mul_smul, Bmat_mul_Nmat0, smul_smul, one_div_mul_cancel h, one_smul]

/-- N is the unique solution of B·N = P when B is invertible. -/
theorem Nmat_unique {Bcc Bcψ Bψc Bψψ p : K} (h : Bcc * Bψψ - Bcψ * Bψc ≠ 0)
    (N : Matrix (Fin 2) (Fin 2) K) (hN : Bmat Bcc Bcψ Bψc Bψψ * N = Pmat p) :
    N = Nmat Bcc Bcψ Bψc Bψψ p := by
  have h1 : Bmat Bcc Bcψ Bψc Bψψ * (N - Nmat Bcc Bcψ Bψc Bψψ p) = 0 := by
    rw [Matrix.mul_sub, hN, Bmat_mul_Nmat h, sub_self]
  have h2 : (Bmat Bcc Bcψ Bψc Bψψ).adjugate * (Bmat Bcc Bcψ Bψc Bψψ *
      (N - Nmat Bcc Bcψ Bψc Bψψ p)) = 0 := by rw [h1, Matrix.mul_zero]
  rw [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul, det_Bmat] at h2
  rcases smul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 h
  · exact sub_eq_zero.mp h3

theorem trace_Nmat (Bcc Bcψ Bψc Bψψ p : K) :
    (Nmat Bcc Bcψ Bψc Bψψ p).trace = Bcc * p / (Bcc * Bψψ - Bcψ * Bψc) := by
  have : (Nmat Bcc Bcψ Bψc Bψψ p).trace =
      1 / (Bcc * Bψψ - Bcψ * Bψc) * 0 + 1 / (Bcc * Bψψ - Bcψ * Bψc) * (Bcc * p) := by
    simp [Nmat, Nmat0, Matrix.trace_fin_two]
  rw [this]; ring

theorem det_Nmat (Bcc Bcψ Bψc Bψψ p : K) : (Nmat Bcc Bcψ Bψc Bψψ p).det = 0 := by
  simp [Nmat, Nmat0, Matrix.det_fin_two]

/-- The eigenvalues of ∂_τZ(0) on Res¹₀ are exactly 0 (the closed state, frozen) and
B_cc·p/det B (the non-closed state): z is a root of the characteristic polynomial iff so. -/
theorem charpoly_roots (Bcc Bcψ Bψc Bψψ p : K) (z : K) :
    z ^ 2 - (Nmat Bcc Bcψ Bψc Bψψ p).trace * z + (Nmat Bcc Bcψ Bψc Bψψ p).det = 0 ↔
      z = 0 ∨ z = Bcc * p / (Bcc * Bψψ - Bcψ * Bψc) := by
  rw [trace_Nmat, det_Nmat, add_zero]
  constructor
  · intro h
    have : z * (z - Bcc * p / (Bcc * Bψψ - Bcψ * Bψc)) = 0 := by rw [← h]; ring
    rcases mul_eq_zero.mp this with h0 | h0
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h0)
  · rintro (rfl | rfl)
    · ring
    · ring

/-- CDDP (3.55)–(3.56): the pairing is block diagonal across C × C_ψ*, so the rate is p/B_ψψ. -/
theorem trace_Nmat_blockdiag {Bcc Bψψ p : K} (hcc : Bcc ≠ 0) (hψψ : Bψψ ≠ 0) :
    (Nmat Bcc 0 0 Bψψ p).trace = p / Bψψ := by
  rw [trace_Nmat]
  field_simp
  ring

/-- The non-closed rate is non-zero iff p ≠ 0: CDDP's non-degeneracy (1.3) ⟺ r₀ ≠ 0. -/
theorem trace_Nmat_ne_zero_iff {Bcc Bcψ Bψc Bψψ p : K} (hcc : Bcc ≠ 0)
    (hdet : Bcc * Bψψ - Bcψ * Bψc ≠ 0) :
    (Nmat Bcc Bcψ Bψc Bψψ p).trace ≠ 0 ↔ p ≠ 0 := by
  rw [trace_Nmat, Ne, div_eq_zero_iff, mul_eq_zero, not_or, not_or]
  constructor
  · intro h; exact h.1.2
  · intro hp; exact ⟨⟨hcc, hp⟩, hdet⟩

/-- Over ℝ, with the rate oriented positive: the (4.22) matrix has w₊ = tr N = r₀ and w₋ = 0
in the notation of `TwinRate` — the two first-order rates of `twin_rate_of_cluster`. -/
theorem wPlus_of_firstVariation {Bcc Bcψ Bψc Bψψ p : ℝ}
    (hr : 0 < (Nmat Bcc Bcψ Bψc Bψψ p).trace) :
    TwinRate.wPlus (Nmat Bcc Bcψ Bψc Bψψ p).trace (Nmat Bcc Bcψ Bψc Bψψ p).det =
      (Nmat Bcc Bcψ Bψc Bψψ p).trace := by
  rw [det_Nmat]; exact TwinRate.wPlus_at_cddp hr

theorem wMinus_of_firstVariation {Bcc Bcψ Bψc Bψψ p : ℝ}
    (hr : 0 < (Nmat Bcc Bcψ Bψc Bψψ p).trace) :
    TwinRate.wMinus (Nmat Bcc Bcψ Bψc Bψψ p).trace (Nmat Bcc Bcψ Bψc Bψψ p).det = 0 := by
  rw [det_Nmat]; exact TwinRate.wMinus_at_cddp hr

end FirstVariation

/-! ## §2 Hadamard: from M(θ,0) = s*·1 to M = s*·1 + τ·N with N continuous at (0,0) -/
namespace Hadamard

theorem Ndiv_zero (M M' : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (sStar : ℝ → ℝ) (θ : ℝ) :
    Ndiv M M' sStar θ 0 = M' θ 0 := by simp [Ndiv]

/-- M = s*·1 + τ·N identically (given M(θ,0) = s*(θ)·1). -/
theorem M_eq (M M' : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (sStar : ℝ → ℝ)
    (h0 : ∀ θ, M θ 0 = sStar θ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) (θ τ : ℝ) :
    M θ τ = sStar θ • (1 : Matrix (Fin 2) (Fin 2) ℝ) + τ • Ndiv M M' sStar θ τ := by
  unfold Ndiv
  split_ifs with hτ
  · subst hτ; rw [h0, zero_smul, add_zero]
  · rw [smul_smul, mul_one_div_cancel hτ, one_smul, add_sub_cancel]

/-- Entrywise mean value theorem: for τ ≠ 0 the difference quotient of an entry equals the
τ-derivative of that entry at some ξ strictly between 0 and τ. -/
theorem entry_slope_eq {f f' : ℝ → ℝ} (hderiv : ∀ t, HasDerivAt f (f' t) t) {τ : ℝ}
    (hτ : τ ≠ 0) : ∃ ξ, |ξ| < |τ| ∧ (f τ - f 0) / τ = f' ξ := by
  have hcont : ∀ s, ContinuousAt f s := fun s => (hderiv s).continuousAt
  rcases lt_or_gt_of_ne hτ with hneg | hpos
  · obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope f f' hneg
      (fun s _ => (hcont s).continuousWithinAt) (fun s _ => hderiv s)
    refine ⟨ξ, ?_, ?_⟩
    · rw [abs_of_neg hneg, abs_of_neg hξ.2]; linarith [hξ.1]
    · rw [hslope, zero_sub, div_neg, ← neg_div, neg_sub]
  · obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope f f' hpos
      (fun s _ => (hcont s).continuousWithinAt) (fun s _ => hderiv s)
    refine ⟨ξ, ?_, ?_⟩
    · rw [abs_of_pos hpos, abs_of_pos hξ.1]; exact hξ.2
    · rw [hslope, sub_zero]

/-- THE HADAMARD STEP. If each entry of M is differentiable in τ with derivative M', M(θ,0) =
s*(θ)·1, and each entry of M' is jointly continuous at (0,0), then each entry of N = Ndiv is
jointly continuous at (0,0) with value M'(0,0). -/
theorem continuousAt_Ndiv_entry (M M' : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (sStar : ℝ → ℝ)
    (h0 : ∀ θ, M θ 0 = sStar θ • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (hderiv : ∀ θ τ i j, HasDerivAt (fun t => M θ t i j) (M' θ τ i j) τ)
    (hM' : ∀ i j, ContinuousAt (fun p : ℝ × ℝ => M' p.1 p.2 i j) (0, 0)) (i j : Fin 2) :
    ContinuousAt (fun p : ℝ × ℝ => Ndiv M M' sStar p.1 p.2 i j) (0, 0) := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.mp (hM' i j) ε hε
  refine ⟨δ, hδ, fun p hp => ?_⟩
  obtain ⟨θ, τ⟩ := p
  have hp' : |θ| < δ ∧ |τ| < δ := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero, sub_zero, max_lt_iff] at hp
    exact hp
  -- the value at (0,0) is M' 0 0 i j
  have hN00 : Ndiv M M' sStar 0 0 i j = M' 0 0 i j := by rw [Ndiv_zero]
  rw [hN00]
  by_cases hτ : τ = 0
  · subst hτ
    rw [Ndiv_zero]
    have hd : dist ((θ, (0 : ℝ)) : ℝ × ℝ) (0, 0) < δ := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero, sub_zero]
      exact max_lt hp'.1 (by rw [abs_zero]; exact hδ)
    exact hball hd
  · -- difference quotient of the entry = derivative at some ξ with |ξ| < |τ|
    have hentry : Ndiv M M' sStar θ τ i j = (M θ τ i j - M θ 0 i j) / τ := by
      simp only [Ndiv, hτ, if_false, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, h0 θ]
      ring
    obtain ⟨ξ, hξ, hslope⟩ := entry_slope_eq (hderiv θ · i j) hτ
    rw [hentry, hslope]
    have hd : dist ((θ, ξ) : ℝ × ℝ) (0, 0) < δ := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero, sub_zero]
      exact max_lt hp'.1 (lt_trans hξ hp'.2)
    exact hball hd

/-- Trace and determinant of N are jointly continuous at (0,0). -/
theorem continuousAt_trace_Ndiv (M M' : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (sStar : ℝ → ℝ)
    (h0 : ∀ θ, M θ 0 = sStar θ • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (hderiv : ∀ θ τ i j, HasDerivAt (fun t => M θ t i j) (M' θ τ i j) τ)
    (hM' : ∀ i j, ContinuousAt (fun p : ℝ × ℝ => M' p.1 p.2 i j) (0, 0)) :
    ContinuousAt (fun p : ℝ × ℝ => (Ndiv M M' sStar p.1 p.2).trace) (0, 0) := by
  have h := continuousAt_Ndiv_entry M M' sStar h0 hderiv hM'
  simp only [Matrix.trace_fin_two]
  exact (h 0 0).add (h 1 1)

theorem continuousAt_det_Ndiv (M M' : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (sStar : ℝ → ℝ)
    (h0 : ∀ θ, M θ 0 = sStar θ • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (hderiv : ∀ θ τ i j, HasDerivAt (fun t => M θ t i j) (M' θ τ i j) τ)
    (hM' : ∀ i j, ContinuousAt (fun p : ℝ × ℝ => M' p.1 p.2 i j) (0, 0)) :
    ContinuousAt (fun p : ℝ × ℝ => (Ndiv M M' sStar p.1 p.2).det) (0, 0) := by
  have h := continuousAt_Ndiv_entry M M' sStar h0 hderiv hM'
  simp only [Matrix.det_fin_two]
  exact ((h 0 0).mul (h 1 1)).sub ((h 0 1).mul (h 1 0))

/-- The characteristic-polynomial data of the ACTUAL cluster matrix M = s*·1 + τ·N are
`TwinRate.clusterTrace`/`clusterDet` with a = tr N, b = det N. -/
theorem trace_M (sStar τ : ℝ) (N : Matrix (Fin 2) (Fin 2) ℝ) :
    (sStar • (1 : Matrix (Fin 2) (Fin 2) ℝ) + τ • N).trace =
      TwinRate.clusterTrace sStar τ N.trace := by
  simp [TwinRate.clusterTrace, Matrix.trace_fin_two]; ring

theorem det_M (sStar τ : ℝ) (N : Matrix (Fin 2) (Fin 2) ℝ) :
    (sStar • (1 : Matrix (Fin 2) (Fin 2) ℝ) + τ • N).det =
      TwinRate.clusterDet sStar τ N.trace N.det := by
  simp [TwinRate.clusterDet, Matrix.det_fin_two, Matrix.trace_fin_two]; ring

/-- CLUSTER ROOTS FOR THE ACTUAL MATRIX: z is a root of the characteristic polynomial of
M(θ,τ) iff z = s*(θ) + τ·w±(tr N, det N). Consumes only M(θ,0) = s*·1 and disc ≥ 0. -/
theorem cluster_roots_M (M M' : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (sStar : ℝ → ℝ)
    (h0 : ∀ θ, M θ 0 = sStar θ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) (θ τ : ℝ)
    (hD : 0 ≤ TwinRate.disc (Ndiv M M' sStar θ τ).trace (Ndiv M M' sStar θ τ).det) (z : ℝ) :
    z ^ 2 - (M θ τ).trace * z + (M θ τ).det = 0 ↔
      z = sStar θ + τ * TwinRate.wPlus (Ndiv M M' sStar θ τ).trace (Ndiv M M' sStar θ τ).det ∨
      z = sStar θ + τ * TwinRate.wMinus (Ndiv M M' sStar θ τ).trace (Ndiv M M' sStar θ τ).det := by
  rw [M_eq M M' sStar h0 θ τ, trace_M, det_M]
  exact TwinRate.cluster_roots hD z

end Hadamard

/-! ## §3 Capstone wrapper: the rate numbers from the (4.22) matrix -/
namespace Capstone

open TwinRate FirstVariation Hadamard OrderCount TorsionCore

end Capstone

end FriedCrossing
