/-
THE TWIN'S RATE FROM THE CLUSTER — sharpening `hrate_nonclosed` (9/07).

Companion to `fried_crossing_9_03` (same leg: Fried at a codimension-one crossing).
That file's capstone consumes `hrate_nonclosed`: "at θ ≠ 0 the non-closed degree-1
branch s_nc(θ,·) is differentiable with ∂_τ s_nc ≥ r₀ for every τ" — a statement no
paper makes (CDDP (4.22)/(4.38) give the rate at θ = 0 only; the θ ≠ 0 version was a
DERIVED continuity step, memo fried_counterexample_rederivation_9_03 A4 / main note §5.1,
covered by residual risk (B)). This file pushes the citation boundary upstream.

Mechanism (finite-dimensional, everything here PROVED). Let Π(θ,τ) be the Riesz projector
of the twisted operator onto the degree-1 spectrum in a fixed disc about 0, rank 2, and
M(θ,τ) the restricted operator. At g_hyp the cluster is the SEMISIMPLE double point s*(θ)
(hdouble), so M(θ,0) = s*(θ)·1 and M(θ,τ) − s*(θ)·1 = τ·N(θ,τ) with N analytic. Writing
a = tr N, b = det N, the eigenvalues of M are exactly s*(θ) + τ·w with w² − a·w + b = 0
(`cluster_roots`). CDDP at (0,0): the first-variation matrix has eigenvalues 0 (the closed
state c stays) and r₀ ≠ 0 (the non-closed twin moves), i.e. a(0,0) = r₀, b(0,0) = 0. The
twin branch is s*(θ) + τ·w₊(a,b), w₊ = (a + √(a²−4b))/2; distinct roots at (0,0) make w₊
and its τ-derivative continuous there, so ∂_τ(twin) = w₊ + τ·∂_τw₊ ≥ r₀/2 on a full
(θ,τ)-neighbourhood of (0,0) (`twin_rate_of_cluster`). That is the shape the capstone
consumed — now a THEOREM from three inputs with clean provenance:

  (i)   cluster projector analytic in (θ,τ)  — sharpened input (B): CDDP §4.1 resolvent
        machinery for the contact-form family + bounded perturbation iθ·ω(X) + Kato;
        enters here as C¹ data (a, b, ∂_τa, ∂_τb continuous at (0,0));
  (ii)  a(0,0) = r₀ ≠ 0                        — CDDP (4.22)/(4.38): the rate at θ = 0;
  (iii) b(0,0) = 0                              — CDDP: the c-row and c-column of the
        first-variation pairing vanish (dc = 0), main note §5.1.

The dependence of the rate on hdouble's SEMISIMPLICITY (M(θ,0) scalar) is now explicit:
it is what makes M − s*·1 divisible by τ.

Bookkeeping consequences. The rate bound is r₀/2 (not r₀), so the crossing bound becomes
σ ≤ 2|s*|/r₀ (`crossing_exists_unique_local`); the derivative control is LOCAL in τ, so
the branch must start within r₀δ/2 of 0 — true for small θ since s*(θ) = Θ(θ²) → 0
(`fried_fails_at_crossing_of_cluster_inputs` asks for continuity of s* at 0 and delivers
[9/16: the capstones `fried_fails_at_crossing_local` and `fried_fails_at_crossing_of_cluster_inputs` were REMOVED
for the Palomar entry as superseded by `fried_counterexample_of_resolvent_inputs`; §6 Saturation and the rate
lemmas remain and are used.]
"for all sufficiently small θ ≠ 0"). Off-crossing Fried (`hfried_off`) is only needed on
|τ| < δ, and the value theorem only needs it eventually near σ (`crossing_value_local`).

§6 (9/08) SATURATION: hdouble's "no other degree-1 resonance in D" — the memo's one uncited
step (ν₁ Selberg factor) — is replaced by a rank count: rank Π₁ = 2 (DGRS Prop 7.7 at θ = 0 +
bounded-twist rank constancy) and two independent states at s* ⇒ the restricted operator is
s*·1 (`Saturation.scalar_of_two_eigenvectors`), hence no third eigenvalue and semisimplicity.

⚡AUDIT CRITERION: ZERO axioms of its own — `#print axioms` on every theorem below lists
only Lean built-ins. This file does NOT touch `fried_crossing_9_03` (still the ledger for
the original flat hypothesis list; both capstones stand).
-/
import B1s.fried_crossing_9_03

set_option linter.style.header false

namespace FriedCrossing

open Filter Topology

/-! ## §1 The rank-2 cluster: eigenvalues as s* + τ·(roots of w² − a w + b) -/
namespace TwinRate

theorem wPlus_add_wMinus (a b : ℝ) : wPlus a b + wMinus a b = a := by
  unfold wPlus wMinus; ring

theorem wPlus_mul_wMinus {a b : ℝ} (h : 0 ≤ disc a b) : wPlus a b * wMinus a b = b := by
  unfold wPlus wMinus
  have := Real.sq_sqrt h
  unfold disc at this ⊢
  nlinarith [this]

theorem wPlus_root {a b : ℝ} (h : 0 ≤ disc a b) :
    wPlus a b ^ 2 - a * wPlus a b + b = 0 := by
  have h1 := wPlus_add_wMinus a b
  have h2 := wPlus_mul_wMinus h
  have : wPlus a b ^ 2 - a * wPlus a b + b =
      wPlus a b ^ 2 - (wPlus a b + wMinus a b) * wPlus a b + wPlus a b * wMinus a b := by
    rw [h1, h2]
  rw [this]; ring

theorem wPlus_sub_wMinus (a b : ℝ) : wPlus a b - wMinus a b = Real.sqrt (disc a b) := by
  unfold wPlus wMinus; ring

theorem wPlus_ne_wMinus {a b : ℝ} (h : 0 < disc a b) : wPlus a b ≠ wMinus a b := by
  intro heq
  have := wPlus_sub_wMinus a b
  rw [heq, sub_self] at this
  exact (Real.sqrt_pos.mpr h).ne this

/-- At the CDDP point (a, b) = (r₀, 0) with r₀ > 0 the two first-order rates are r₀ and 0. -/
theorem wPlus_at_cddp {r₀ : ℝ} (hr₀ : 0 < r₀) : wPlus r₀ 0 = r₀ := by
  unfold wPlus disc
  rw [mul_zero, sub_zero, Real.sqrt_sq hr₀.le]; ring

theorem wMinus_at_cddp {r₀ : ℝ} (hr₀ : 0 < r₀) : wMinus r₀ 0 = 0 := by
  unfold wMinus disc
  rw [mul_zero, sub_zero, Real.sqrt_sq hr₀.le]; ring

/-- Trace and determinant of M = s*·1 + τ·N in terms of a = tr N, b = det N. -/
def clusterTrace (sStar τ a : ℝ) : ℝ := 2 * sStar + τ * a
def clusterDet (sStar τ a b : ℝ) : ℝ := sStar ^ 2 + sStar * τ * a + τ ^ 2 * b

/-- The characteristic polynomial of the cluster factors through the two branches:
z² − (tr M) z + det M = (z − (s* + τ w₊))(z − (s* + τ w₋)). -/
theorem charpoly_factor {sStar τ a b : ℝ} (h : 0 ≤ disc a b) (z : ℝ) :
    z ^ 2 - clusterTrace sStar τ a * z + clusterDet sStar τ a b =
      (z - (sStar + τ * wPlus a b)) * (z - (sStar + τ * wMinus a b)) := by
  have h1 := wPlus_add_wMinus a b
  have h2 := wPlus_mul_wMinus h
  unfold clusterTrace clusterDet
  have : (z - (sStar + τ * wPlus a b)) * (z - (sStar + τ * wMinus a b)) =
      z ^ 2 - (2 * sStar + τ * (wPlus a b + wMinus a b)) * z +
        (sStar ^ 2 + sStar * τ * (wPlus a b + wMinus a b) + τ ^ 2 * (wPlus a b * wMinus a b)) := by
    ring
  rw [this, h1, h2]

/-- The eigenvalues of the cluster are EXACTLY the two branches (no third resonance in the
disc): z is a root of the characteristic polynomial iff z = s* + τ w₊ or z = s* + τ w₋. -/
theorem cluster_roots {sStar τ a b : ℝ} (h : 0 ≤ disc a b) (z : ℝ) :
    z ^ 2 - clusterTrace sStar τ a * z + clusterDet sStar τ a b = 0 ↔
      z = sStar + τ * wPlus a b ∨ z = sStar + τ * wMinus a b := by
  rw [charpoly_factor h, mul_eq_zero, sub_eq_zero, sub_eq_zero]

/-- For τ ≠ 0 and positive discriminant the two branches are distinct: the twin has
separated from the closed state. -/
theorem branches_ne {sStar τ a b : ℝ} (hτ : τ ≠ 0) (h : 0 < disc a b) :
    sStar + τ * wPlus a b ≠ sStar + τ * wMinus a b := by
  intro heq
  have : τ * (wPlus a b - wMinus a b) = 0 := by linarith
  rcases mul_eq_zero.mp this with h0 | h0
  · exact hτ h0
  · exact wPlus_ne_wMinus h (sub_eq_zero.mp h0)

/-! ## §2 The twin branch and its τ-derivative -/

theorem twin_zero (sStar : ℝ → ℝ) (a b : ℝ → ℝ → ℝ) (θ : ℝ) : twin sStar a b θ 0 = sStar θ := by
  simp [twin]

theorem hasDerivAt_disc {A B : ℝ → ℝ} {a' b' τ : ℝ} (hA : HasDerivAt A a' τ)
    (hB : HasDerivAt B b' τ) :
    HasDerivAt (fun t => disc (A t) (B t)) (2 * A τ * a' - 4 * b') τ := by
  have h1 : HasDerivAt (fun t => A t * A t) (a' * A τ + A τ * a') τ := hA.mul hA
  have h2 : HasDerivAt (fun t => 4 * B t) (4 * b') τ := hB.const_mul 4
  have h3 := h1.sub h2
  have hfun : (fun t => disc (A t) (B t)) = fun t => A t * A t - 4 * B t := by
    funext t; simp [disc, sq]
  rw [hfun]
  exact h3.congr_deriv (by ring)

theorem hasDerivAt_wPlus {A B : ℝ → ℝ} {a' b' τ : ℝ} (hA : HasDerivAt A a' τ)
    (hB : HasDerivAt B b' τ) (hD : 0 < disc (A τ) (B τ)) :
    HasDerivAt (fun t => wPlus (A t) (B t)) (dwPlus (A τ) (B τ) a' b') τ := by
  unfold wPlus dwPlus
  have hs : HasDerivAt (fun t => Real.sqrt (disc (A t) (B t)))
      ((2 * A τ * a' - 4 * b') / (2 * Real.sqrt (disc (A τ) (B τ)))) τ :=
    (hasDerivAt_disc hA hB).sqrt hD.ne'
  exact (hA.add hs).div_const 2

theorem hasDerivAt_twin {sStar : ℝ → ℝ} {a b a' b' : ℝ → ℝ → ℝ} {θ τ : ℝ}
    (hA : HasDerivAt (a θ) (a' θ τ) τ) (hB : HasDerivAt (b θ) (b' θ τ) τ)
    (hD : 0 < disc (a θ τ) (b θ τ)) :
    HasDerivAt (twin sStar a b θ) (dtwin (a θ τ) (b θ τ) (a' θ τ) (b' θ τ) τ) τ := by
  unfold twin dtwin
  have hw := hasDerivAt_wPlus hA hB hD
  have hτ : HasDerivAt (fun t : ℝ => t) 1 τ := hasDerivAt_id τ
  have hprod := hτ.mul hw
  have := (hasDerivAt_const τ (sStar θ)).add hprod
  exact this.congr_deriv (by ring)

/-! ## §3 Continuity of the rate at the CDDP point -/

theorem continuousAt_wPlus (p : ℝ × ℝ) :
    ContinuousAt (fun q : ℝ × ℝ => wPlus q.1 q.2) p := by
  unfold wPlus disc
  fun_prop

theorem continuousAt_dwPlus {p : ℝ × ℝ × ℝ × ℝ} (hD : 0 < disc p.1 p.2.1) :
    ContinuousAt (fun q : ℝ × ℝ × ℝ × ℝ => dwPlus q.1 q.2.1 q.2.2.1 q.2.2.2) p := by
  unfold dwPlus
  have hne : 2 * Real.sqrt (disc p.1 p.2.1) ≠ 0 :=
    mul_ne_zero two_ne_zero (Real.sqrt_pos.mpr hD).ne'
  unfold disc at hne ⊢
  fun_prop (disch := exact hne)

/-- THE RATE LEMMA. From (i) C¹ cluster data a, b (trace and determinant of N, with
τ-derivatives a', b', all four continuous at (0,0)), (ii) a(0,0) = r₀ > 0, (iii) b(0,0) = 0:
on a full neighbourhood |θ| < ε, |τ| < ε the discriminant is positive, the twin branch is
differentiable in τ with derivative `dtwin`, and that derivative lies in [r₀/2, 2r₀]. -/
theorem twin_rate_of_cluster (sStar : ℝ → ℝ) (a b a' b' : ℝ → ℝ → ℝ) {r₀ : ℝ}
    (hr₀ : 0 < r₀)
    (hderiv_a : ∀ θ τ, HasDerivAt (a θ) (a' θ τ) τ)
    (hderiv_b : ∀ θ τ, HasDerivAt (b θ) (b' θ τ) τ)
    (hcont_a : ContinuousAt (Function.uncurry a) (0, 0))
    (hcont_b : ContinuousAt (Function.uncurry b) (0, 0))
    (hcont_a' : ContinuousAt (Function.uncurry a') (0, 0))
    (hcont_b' : ContinuousAt (Function.uncurry b') (0, 0))
    (ha0 : a 0 0 = r₀) (hb0 : b 0 0 = 0) :
    ∃ ε > 0, ∀ θ τ : ℝ, |θ| < ε → |τ| < ε →
      0 < disc (a θ τ) (b θ τ) ∧
      HasDerivAt (twin sStar a b θ) (dtwin (a θ τ) (b θ τ) (a' θ τ) (b' θ τ) τ) τ ∧
      r₀ / 2 ≤ dtwin (a θ τ) (b θ τ) (a' θ τ) (b' θ τ) τ ∧
      dtwin (a θ τ) (b θ τ) (a' θ τ) (b' θ τ) τ ≤ 2 * r₀ := by
  -- the data map (θ,τ) ↦ (a, b, a', b') and the discriminant along it
  set Φ : ℝ × ℝ → ℝ × ℝ × ℝ × ℝ :=
    fun p => (a p.1 p.2, b p.1 p.2, a' p.1 p.2, b' p.1 p.2) with hΦ
  have hΦc : ContinuousAt Φ (0, 0) :=
    hcont_a.prodMk (hcont_b.prodMk (hcont_a'.prodMk hcont_b'))
  have hdisc0 : 0 < disc (a 0 0) (b 0 0) := by
    rw [ha0, hb0]; unfold disc; nlinarith
  have hdiscc : ContinuousAt (fun p : ℝ × ℝ => disc (a p.1 p.2) (b p.1 p.2)) (0, 0) := by
    unfold disc
    have h1 : ContinuousAt (fun p : ℝ × ℝ => a p.1 p.2) (0, 0) := hcont_a
    have h2 : ContinuousAt (fun p : ℝ × ℝ => b p.1 p.2) (0, 0) := hcont_b
    exact (h1.pow 2).sub (continuousAt_const.mul h2)
  -- eventually positive discriminant
  have hev1 : ∀ᶠ p : ℝ × ℝ in 𝓝 (0, 0), 0 < disc (a p.1 p.2) (b p.1 p.2) :=
    hdiscc.eventually (lt_mem_nhds hdisc0)
  -- the derivative expression as a function of (θ,τ), continuous at (0,0), value r₀
  set D : ℝ × ℝ → ℝ := fun p => dtwin (a p.1 p.2) (b p.1 p.2) (a' p.1 p.2) (b' p.1 p.2) p.2
    with hD
  have hDc : ContinuousAt D (0, 0) := by
    have hw : ContinuousAt (fun p : ℝ × ℝ => wPlus (a p.1 p.2) (b p.1 p.2)) (0, 0) := by
      have hab : ContinuousAt (fun p : ℝ × ℝ => (a p.1 p.2, b p.1 p.2)) (0, 0) :=
        hcont_a.prodMk hcont_b
      exact (continuousAt_wPlus _).comp hab
    have hdw : ContinuousAt (fun p : ℝ × ℝ => dwPlus (a p.1 p.2) (b p.1 p.2) (a' p.1 p.2)
        (b' p.1 p.2)) (0, 0) := by
      have := (continuousAt_dwPlus (p := Φ (0, 0)) hdisc0).comp hΦc
      exact this
    have hτ : ContinuousAt (fun p : ℝ × ℝ => p.2) (0, 0) := continuousAt_snd
    exact hw.add (hτ.mul hdw)
  have hD0 : D (0, 0) = r₀ := by
    simp only [hD, dtwin, ha0, hb0, zero_mul, add_zero]
    exact wPlus_at_cddp hr₀
  have hev2 : ∀ᶠ p : ℝ × ℝ in 𝓝 (0, 0), D p ∈ Set.Ioo (r₀ / 2) (2 * r₀) := by
    apply hDc.eventually
    rw [hD0]
    exact Ioo_mem_nhds (by linarith) (by linarith)
  -- extract a ball
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (hev1.and hev2)
  refine ⟨ε, hε, fun θ τ hθ hτ => ?_⟩
  have hmem : dist ((θ, τ) : ℝ × ℝ) (0, 0) < ε := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero, sub_zero]
    exact max_lt hθ hτ
  obtain ⟨hpos, hgt⟩ := hball hmem
  exact ⟨hpos, hasDerivAt_twin (hderiv_a θ τ) (hderiv_b θ τ) hpos, hgt.1.le, hgt.2.le⟩

end TwinRate

/-! ## §4 Local versions of P3 and P4 -/
namespace Crossing

/-- LOCAL crossing lemma. A real branch differentiable on |τ| < δ with ∂_τ s ≥ r > 0
there, s(0) < 0 and |s(0)| < rδ, crosses 0 exactly once in (−δ, δ), at
σ ∈ (0, |s(0)|/r] ⊂ (0, δ). -/
theorem crossing_exists_unique_local {s ds : ℝ → ℝ} {r δ : ℝ} (hr : 0 < r)
    (hderiv : ∀ τ, |τ| < δ → HasDerivAt s (ds τ) τ) (hlow : ∀ τ, |τ| < δ → r ≤ ds τ)
    (hs0 : s 0 < 0) (hsmall : |s 0| < r * δ) :
    ∃ σ, 0 < σ ∧ σ ≤ |s 0| / r ∧ σ < δ ∧ s σ = 0 ∧ ∀ τ, |τ| < δ → s τ = 0 → τ = σ := by
  have hmemI : ∀ τ, τ ∈ Set.Ioo (-δ) δ ↔ |τ| < δ := fun τ => by
    rw [Set.mem_Ioo, abs_lt]
  have hcontOn : ContinuousOn s (Set.Ioo (-δ) δ) := fun τ hτ =>
    (hderiv τ ((hmemI τ).mp hτ)).continuousAt.continuousWithinAt
  have hmono : StrictMonoOn s (Set.Ioo (-δ) δ) := by
    refine strictMonoOn_of_deriv_pos (convex_Ioo _ _) hcontOn fun τ hτ => ?_
    rw [interior_Ioo] at hτ
    have hτ' := (hmemI τ).mp hτ
    rw [(hderiv τ hτ').deriv]
    exact lt_of_lt_of_le hr (hlow τ hτ')
  set T := -s 0 / r with hT
  have habs : |s 0| = -s 0 := abs_of_neg hs0
  have hTpos : 0 < T := div_pos (neg_pos.mpr hs0) hr
  have hTlt : T < δ := by
    rw [hT, div_lt_iff₀ hr]; rw [habs] at hsmall; linarith
  have hrT : r * T = -s 0 := by rw [hT, mul_div_cancel₀ _ hr.ne']
  -- MVT on [0, T]: s T − s 0 = ds c · T ≥ r T = −s 0
  have hIcc : Set.Icc 0 T ⊆ Set.Ioo (-δ) δ := fun τ hτ =>
    ⟨by linarith [hτ.1], lt_of_le_of_lt hτ.2 hTlt⟩
  have hcontIcc : ContinuousOn s (Set.Icc 0 T) := hcontOn.mono hIcc
  have hderivIoo : ∀ τ ∈ Set.Ioo 0 T, HasDerivAt s (ds τ) τ := fun τ hτ =>
    hderiv τ ((hmemI τ).mp (hIcc (Set.Ioo_subset_Icc_self hτ)))
  obtain ⟨c, hc, hcslope⟩ := exists_hasDerivAt_eq_slope s ds hTpos hcontIcc hderivIoo
  have hc' : |c| < δ := (hmemI c).mp (hIcc (Set.Ioo_subset_Icc_self hc))
  have hsT : 0 ≤ s T := by
    have h1 : r ≤ ds c := hlow c hc'
    have h2 : ds c * (T - 0) = s T - s 0 := by
      rw [hcslope, sub_zero]; exact div_mul_cancel₀ _ hTpos.ne'
    have h3 : r * T ≤ ds c * T := mul_le_mul_of_nonneg_right h1 hTpos.le
    simp only [sub_zero] at h2
    linarith
  obtain ⟨σ, hσmem, hσ⟩ : (0 : ℝ) ∈ s '' Set.Icc 0 T :=
    intermediate_value_Icc hTpos.le hcontIcc ⟨hs0.le, hsT⟩
  have hσpos : 0 < σ := by
    rcases hσmem.1.lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h] at hσ; linarith
  have hσlt : σ < δ := lt_of_le_of_lt hσmem.2 hTlt
  refine ⟨σ, hσpos, ?_, hσlt, hσ, fun τ hτ hτ0 => ?_⟩
  · rw [habs]; exact hσmem.2
  · exact hmono.injOn ((hmemI τ).mpr hτ) ((hmemI σ).mpr (by rw [abs_lt]; constructor <;> linarith))
      (hτ0.trans hσ.symm)

end Crossing

namespace RateRatio

/-- `crossing_value` with the off-crossing identity only required EVENTUALLY near σ. -/
theorem crossing_value_local {z p R : ℝ → ℝ} {a b σ τR : ℝ}
    (hz : LinearArrival z a σ) (hp : LinearArrival p b σ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hoff : ∀ᶠ τ in 𝓝[≠] σ, R τ * z τ / p τ = τR) (hR : ContinuousAt R σ) :
    R σ = τR * (b / a) := by
  have hpz := ratio_tendsto hp hz ha
  have hlim : Tendsto R (𝓝[≠] σ) (𝓝 (τR * (b / a))) := by
    refine (hpz.const_mul τR).congr' ?_
    filter_upwards [hoff, eventually_ne_zero_of_linearArrival hz ha,
      eventually_ne_zero_of_linearArrival hp hb] with τ hτ hzτ hpτ
    rw [← hτ]
    field_simp
  exact tendsto_nhds_unique (hR.tendsto.mono_left nhdsWithin_le_nhds) hlim

end RateRatio

/-! ## §5 Capstones consuming the rate lemma -/
namespace Capstone

open TorsionCore OrderCount Crossing RateRatio TwinRate

end Capstone

/-! ## §6 (9/08) SATURATION — hdouble's "nothing else in the disc" from the rank count

The one uncited step inside hdouble (memo: the ν₁ Selberg factor Z_{S,ν₁}(λ+1) has no zero
in a θ-independent disc D about 0) is bypassed by counting. Inputs, both ALREADY in the
ledger: (r) the degree-1 Riesz projector Π₁(θ,0) onto D has rank 2 — at θ = 0 this is DGRS
Prop 7.7 (m₁(0) = 2·dim H¹ = 2b₁ = 2) plus discreteness of resonances (choose D), and the rank
is constant in θ because the twist iθ·ω(X) is a bounded perturbation (the θ-half of input
(B)); (e) two linearly independent states d₀f, I·d₀f at s*(θ) in ran Π₁ (rederivation A2,
constructed from the degree-0 state). Conclusion: the restricted operator IS s*·1 — every
eigenvalue in D equals s*, geometric = algebraic multiplicity = 2, no Jordan block — which
is exactly the `M(θ,0) = s*·1` that §2 of this file consumed as the divisibility premise.
The ν₁ factor is never analysed. -/
namespace Saturation

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

/-- Two independent eigenvectors with the same eigenvalue in a 2-dimensional space force the
operator to be that scalar. -/
theorem scalar_of_two_eigenvectors (hdim : Module.finrank K V = 2) (T : V →ₗ[K] V) (s : K)
    (v₁ v₂ : V) (hind : LinearIndependent K ![v₁, v₂])
    (h₁ : T v₁ = s • v₁) (h₂ : T v₂ = s • v₂) :
    T = s • LinearMap.id := by
  have hcard : Fintype.card (Fin 2) = Module.finrank K V := by simp [hdim]
  let b := basisOfLinearIndependentOfCardEqFinrank hind hcard
  have hb : ∀ i, b i = ![v₁, v₂] i := fun i => by
    simp [b, coe_basisOfLinearIndependentOfCardEqFinrank]
  refine b.ext fun i => ?_
  rw [hb]
  fin_cases i
  · simpa using h₁
  · simpa using h₂

/-- SATURATION: under the same hypotheses every eigenvalue of T equals s — there is no third
resonance in the disc. -/
theorem eigenvalue_eq_of_saturated (hdim : Module.finrank K V = 2) (T : V →ₗ[K] V) (s : K)
    (v₁ v₂ : V) (hind : LinearIndependent K ![v₁, v₂])
    (h₁ : T v₁ = s • v₁) (h₂ : T v₂ = s • v₂)
    {μ : K} {v : V} (hv : v ≠ 0) (hμ : T v = μ • v) : μ = s := by
  have hT := scalar_of_two_eigenvectors hdim T s v₁ v₂ hind h₁ h₂
  rw [hT] at hμ
  simp only [LinearMap.smul_apply, LinearMap.id_coe, id_eq] at hμ
  have : (μ - s) • v = 0 := by rw [sub_smul, hμ, sub_self]
  rcases smul_eq_zero.mp this with h | h
  · exact (sub_eq_zero.mp h)
  · exact absurd h hv

/-- No Jordan block: (T − s)² = 0 already at the first power, so algebraic multiplicity of s
is exactly the rank 2 = its geometric multiplicity (SEMISIMPLE double point — the premise
`M(θ,0) = s*·1` of §2). -/
theorem semisimple_of_saturated (hdim : Module.finrank K V = 2) (T : V →ₗ[K] V) (s : K)
    (v₁ v₂ : V) (hind : LinearIndependent K ![v₁, v₂])
    (h₁ : T v₁ = s • v₁) (h₂ : T v₂ = s • v₂) :
    T - s • LinearMap.id = 0 := by
  rw [scalar_of_two_eigenvectors hdim T s v₁ v₂ hind h₁ h₂, sub_self]

end Saturation

end FriedCrossing
