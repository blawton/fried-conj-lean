/-
THE CLUSTER MATRICES AS PRIMITIVES — input (B) collapsed to ONE regularity fact (9/10).

Companion to the three crossing leg files (same leg). Until now the statement file consumed FOUR
uncited regularity bundles — `ClusterC1`, `TraceDetC1`, `PureSumC2`, `PureProdC3` — one each for
M, N = (M − s*·1)/τ, e₁ and e₂. They are not independent: the pure-quadratic coefficients are
POLYNOMIALS in the entries of the two cluster matrices,
    e₁ = c₁(A) − tr M,      e₂ = c₂(A) − det M − (tr M)·e₁,
(c_k = characteristic coefficients of the 4×4 degree-2 cluster matrix A, since s_cl + s_nc = tr M
and s_cl·s_nc = det M for the two locked branches = the eigenvalues of the 2×2 degree-1 cluster
matrix M), and N is the Hadamard quotient of M. So joint C³ of the ENTRIES of M and A implies all
four. This file proves that (§2–§4), and makes the matrices the primitive objects of the ledger:
  §1 ClusterMatrix — charpoly of a 4×4 matrix in the quartic normal form; e₁, e₂ from (A, M);
     C^k of det / charpoly coefficients / trace in the entries.
  §2 Regularity — partial derivatives pτ, pθ of a jointly C^{k+1} function are jointly C^k with the
     expected `HasDerivAt`; continuous functions are bounded on the unit square.
  §3 HQuot — the Hadamard quotient q(τ) = (f(τ) − f(0))/τ of a C² function is C¹, with
     q'(0) = f''(0)/2 (two-MVT Taylor), and its derivative is jointly continuous in a parameter.
  §4 Derived bundles — `ClusterC3 ⇒ ClusterC1 ∧ TraceDetC1 ∧ PureSumC2 ∧ PureProdC3`.
  §5 Spectral facts on the matrices: mirror (spec A(θ,0) = {s*,s*,s*,−s*}) ⇒ e₁(θ,0) = 0,
     e₂(θ,0) = −s*²; pinning (spec A(0,τ) = {0,0,0,twin}, det M(0,τ) = 0) ⇒ e₁(0,τ) = e₂(0,τ) = 0;
     exactness dictionary: c₂ = 2c₁ with c_k = algebraic multiplicity of 0 in the degree-k cluster
     matrix ⇒ at a crossing e₂ = 0 and e₁ ≠ 0 (the former `hexactZero`, `hgeneric`).
  §6 Capstone `fried_fails_at_crossing_of_matrix_inputs`.

⚡AUDIT CRITERION: ZERO axioms of its own — `#print axioms` on every theorem = built-ins only.
-/
import B1s.fried_crossing_purezeros_9_08

set_option linter.style.header false

namespace FriedCrossing

open Filter Topology Matrix Polynomial

/-! ## §1 The cluster matrices and the pure quadratic -/
namespace ClusterMatrix

theorem charpoly_natDegree (A : Matrix (Fin 4) (Fin 4) ℝ) : A.charpoly.natDegree = 4 := by
  rw [charpoly_natDegree_eq_dim, Fintype.card_fin]

/-- The characteristic polynomial of the degree-2 cluster matrix IS the quartic of the pure-zeros
file. -/
theorem eval_charpoly_eq_quartic (A : Matrix (Fin 4) (Fin 4) ℝ) (z : ℝ) :
    A.charpoly.eval z = PureZeros.quartic (c₁ A) (c₂ A) (c₃ A) (c₄ A) z := by
  have hlead : A.charpoly.coeff 4 = 1 := by
    have := (charpoly_monic A).coeff_natDegree
    rwa [charpoly_natDegree] at this
  rw [eval_eq_sum_range, charpoly_natDegree]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, PureZeros.quartic, c₁, c₂, c₃, c₄,
    hlead]
  ring

/-- The 2×2 characteristic polynomial: z² − (tr M)z + det M. -/
theorem eval_charpoly_fin_two (M : Matrix (Fin 2) (Fin 2) ℝ) (z : ℝ) :
    M.charpoly.eval z = z ^ 2 - M.trace * z + M.det := by
  rw [eval_charpoly]
  simp [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.scalar_apply]
  ring

/-- With the locked branches the eigenvalues of M, these are the pure-zeros file's `e₁of`,
`e₂of`. -/
theorem E₁_eq (A : Matrix (Fin 4) (Fin 4) ℝ) (M : Matrix (Fin 2) (Fin 2) ℝ) {scl snc : ℝ}
    (hs : scl + snc = M.trace) : E₁ A M = PureZeros.e₁of (c₁ A) scl snc := by
  unfold E₁ PureZeros.e₁of; rw [← hs]; ring

theorem E₂_eq (A : Matrix (Fin 4) (Fin 4) ℝ) (M : Matrix (Fin 2) (Fin 2) ℝ) {scl snc : ℝ}
    (hs : scl + snc = M.trace) (hp : scl * snc = M.det) :
    E₂ A M = PureZeros.e₂of (c₁ A) (c₂ A) scl snc := by
  unfold E₂ E₁ PureZeros.e₂of PureZeros.e₁of; rw [← hs, ← hp]; ring

theorem trace_smul_one (s : ℝ) : (s • (1 : Matrix (Fin 2) (Fin 2) ℝ)).trace = 2 * s := by
  rw [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin]; push_cast; ring

theorem det_smul_one (s : ℝ) : (s • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det = s ^ 2 := by
  rw [Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one]

section Smoothness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : WithTop ℕ∞}

/-- The determinant is a polynomial in the entries. -/
theorem contDiff_det {n : Type*} [Fintype n] [DecidableEq n] {A : E → Matrix n n ℝ}
    (h : ∀ i j, ContDiff ℝ k fun x => A x i j) : ContDiff ℝ k fun x => (A x).det := by
  simp only [Matrix.det_apply']
  exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => h _ _)

/-- Characteristic coefficients are signed sums of principal minors (Mathlib), hence polynomial
in the entries. -/
theorem contDiff_charpoly_coeff {A : E → Matrix (Fin 4) (Fin 4) ℝ}
    (h : ∀ i j, ContDiff ℝ k fun x => A x i j) (m : ℕ) (hm : m ≤ 4) :
    ContDiff ℝ k fun x => (A x).charpoly.coeff (4 - m) := by
  have heq : (fun x => (A x).charpoly.coeff (4 - m)) = fun x =>
      (-1 : ℝ) ^ m * ∑ s ∈ (Finset.univ : Finset (Fin 4)).powersetCard m,
        ((A x).submatrix (Subtype.val : s → Fin 4) (Subtype.val : s → Fin 4)).det := by
    funext x
    have := charpoly_coeff_eq_sum_minors (A x) m (by simpa using hm)
    simpa [Fintype.card_fin] using this
  rw [heq]
  exact contDiff_const.mul (ContDiff.sum fun s _ => contDiff_det fun i j => h _ _)

theorem contDiff_c₁ {A : E → Matrix (Fin 4) (Fin 4) ℝ}
    (h : ∀ i j, ContDiff ℝ k fun x => A x i j) : ContDiff ℝ k fun x => c₁ (A x) :=
  (contDiff_charpoly_coeff h 1 (by norm_num)).neg

theorem contDiff_c₂ {A : E → Matrix (Fin 4) (Fin 4) ℝ}
    (h : ∀ i j, ContDiff ℝ k fun x => A x i j) : ContDiff ℝ k fun x => c₂ (A x) :=
  contDiff_charpoly_coeff h 2 (by norm_num)

theorem contDiff_trace_fin_two {M : E → Matrix (Fin 2) (Fin 2) ℝ}
    (h : ∀ i j, ContDiff ℝ k fun x => M x i j) : ContDiff ℝ k fun x => (M x).trace := by
  simp only [Matrix.trace_fin_two]; exact (h 0 0).add (h 1 1)

theorem contDiff_det_fin_two {M : E → Matrix (Fin 2) (Fin 2) ℝ}
    (h : ∀ i j, ContDiff ℝ k fun x => M x i j) : ContDiff ℝ k fun x => (M x).det := by
  simp only [Matrix.det_fin_two]; exact ((h 0 0).mul (h 1 1)).sub ((h 0 1).mul (h 1 0))

theorem contDiff_E₁ {A : E → Matrix (Fin 4) (Fin 4) ℝ} {M : E → Matrix (Fin 2) (Fin 2) ℝ}
    (hA : ∀ i j, ContDiff ℝ k fun x => A x i j) (hM : ∀ i j, ContDiff ℝ k fun x => M x i j) :
    ContDiff ℝ k fun x => E₁ (A x) (M x) :=
  (contDiff_c₁ hA).sub (contDiff_trace_fin_two hM)

theorem contDiff_E₂ {A : E → Matrix (Fin 4) (Fin 4) ℝ} {M : E → Matrix (Fin 2) (Fin 2) ℝ}
    (hA : ∀ i j, ContDiff ℝ k fun x => A x i j) (hM : ∀ i j, ContDiff ℝ k fun x => M x i j) :
    ContDiff ℝ k fun x => E₂ (A x) (M x) :=
  ((contDiff_c₂ hA).sub (contDiff_det_fin_two hM)).sub
    ((contDiff_trace_fin_two hM).mul (contDiff_E₁ hA hM))

end Smoothness

end ClusterMatrix

/-! ## §2 Partial derivatives of jointly C^k functions -/
namespace Regularity

theorem hasDerivAt_slice_τ {f : ℝ → ℝ → ℝ} (hf : Differentiable ℝ fun q : ℝ × ℝ => f q.1 q.2)
    (θ τ : ℝ) :
    HasDerivAt (fun t => f θ t) (fderiv ℝ (fun q : ℝ × ℝ => f q.1 q.2) (θ, τ) (0, 1)) τ := by
  have h1 := (hf (θ, τ)).hasFDerivAt
  have h2 : HasDerivAt (fun t : ℝ => ((θ, t) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) τ :=
    (hasDerivAt_const τ θ).prodMk (hasDerivAt_id τ)
  exact HasFDerivAt.comp_hasDerivAt (f := fun t : ℝ => ((θ, t) : ℝ × ℝ)) τ h1 h2

theorem hasDerivAt_slice_θ {f : ℝ → ℝ → ℝ} (hf : Differentiable ℝ fun q : ℝ × ℝ => f q.1 q.2)
    (θ τ : ℝ) :
    HasDerivAt (fun s => f s τ) (fderiv ℝ (fun q : ℝ × ℝ => f q.1 q.2) (θ, τ) (1, 0)) θ := by
  have h1 := (hf (θ, τ)).hasFDerivAt
  have h2 : HasDerivAt (fun s : ℝ => ((s, τ) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) θ :=
    (hasDerivAt_id θ).prodMk (hasDerivAt_const θ τ)
  exact HasFDerivAt.comp_hasDerivAt (f := fun s : ℝ => ((s, τ) : ℝ × ℝ)) θ h1 h2

theorem pτ_eq {f : ℝ → ℝ → ℝ} (hf : Differentiable ℝ fun q : ℝ × ℝ => f q.1 q.2) (θ τ : ℝ) :
    pτ f θ τ = fderiv ℝ (fun q : ℝ × ℝ => f q.1 q.2) (θ, τ) (0, 1) :=
  (hasDerivAt_slice_τ hf θ τ).deriv

theorem pθ_eq {f : ℝ → ℝ → ℝ} (hf : Differentiable ℝ fun q : ℝ × ℝ => f q.1 q.2) (θ τ : ℝ) :
    pθ f θ τ = fderiv ℝ (fun q : ℝ × ℝ => f q.1 q.2) (θ, τ) (1, 0) :=
  (hasDerivAt_slice_θ hf θ τ).deriv

theorem hasDerivAt_pτ {f : ℝ → ℝ → ℝ} (hf : Differentiable ℝ fun q : ℝ × ℝ => f q.1 q.2)
    (θ τ : ℝ) : HasDerivAt (fun t => f θ t) (pτ f θ τ) τ := by
  rw [pτ_eq hf]; exact hasDerivAt_slice_τ hf θ τ

theorem hasDerivAt_pθ {f : ℝ → ℝ → ℝ} (hf : Differentiable ℝ fun q : ℝ × ℝ => f q.1 q.2)
    (θ τ : ℝ) : HasDerivAt (fun s => f s τ) (pθ f θ τ) θ := by
  rw [pθ_eq hf]; exact hasDerivAt_slice_θ hf θ τ

theorem differentiable_of_contDiff {f : ℝ → ℝ → ℝ} {m n : WithTop ℕ∞} (hmn : m + 1 ≤ n)
    (hf : ContDiff ℝ n fun q : ℝ × ℝ => f q.1 q.2) :
    Differentiable ℝ fun q : ℝ × ℝ => f q.1 q.2 :=
  (hf.of_le (le_trans le_add_self hmn)).differentiable one_ne_zero

/-- One derivative down: the τ-partial of a jointly C^{m+1} function is jointly C^m. -/
theorem contDiff_pτ {f : ℝ → ℝ → ℝ} {m n : WithTop ℕ∞} (hmn : m + 1 ≤ n)
    (hf : ContDiff ℝ n fun q : ℝ × ℝ => f q.1 q.2) :
    ContDiff ℝ m fun q : ℝ × ℝ => pτ f q.1 q.2 := by
  have hd := differentiable_of_contDiff hmn hf
  have : (fun q : ℝ × ℝ => pτ f q.1 q.2) =
      fun q : ℝ × ℝ => fderiv ℝ (fun q : ℝ × ℝ => f q.1 q.2) q (0, 1) := by
    funext q; exact pτ_eq hd q.1 q.2
  rw [this]
  exact (hf.fderiv_right hmn).clm_apply contDiff_const

theorem contDiff_pθ {f : ℝ → ℝ → ℝ} {m n : WithTop ℕ∞} (hmn : m + 1 ≤ n)
    (hf : ContDiff ℝ n fun q : ℝ × ℝ => f q.1 q.2) :
    ContDiff ℝ m fun q : ℝ × ℝ => pθ f q.1 q.2 := by
  have hd := differentiable_of_contDiff hmn hf
  have : (fun q : ℝ × ℝ => pθ f q.1 q.2) =
      fun q : ℝ × ℝ => fderiv ℝ (fun q : ℝ × ℝ => f q.1 q.2) q (1, 0) := by
    funext q; exact pθ_eq hd q.1 q.2
  rw [this]
  exact (hf.fderiv_right hmn).clm_apply contDiff_const

/-- A continuous function is bounded on the unit square. -/
theorem bound_on_square {g : ℝ → ℝ → ℝ} (hg : Continuous fun q : ℝ × ℝ => g q.1 q.2) :
    ∃ K : ℝ, 0 < K ∧ ∀ θ τ : ℝ, |θ| < 1 → |τ| < 1 → |g θ τ| ≤ K := by
  have hK : IsCompact (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
  refine ⟨max C 1, lt_max_of_lt_right one_pos, fun θ τ hθ hτ => ?_⟩
  have hmem : ((θ, τ) : ℝ × ℝ) ∈ Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1 := by
    rw [abs_lt] at hθ hτ
    exact ⟨⟨hθ.1.le, hθ.2.le⟩, ⟨hτ.1.le, hτ.2.le⟩⟩
  have := hC (θ, τ) hmem
  rw [Real.norm_eq_abs] at this
  exact le_trans this (le_max_left _ _)

end Regularity

/-! ## §3 The Hadamard quotient of a C² function is C¹ -/
namespace HQuot

/-- Mean value theorem with the intermediate point strictly between 0 and τ. -/
theorem slope_eq_strict {f f' : ℝ → ℝ} (hderiv : ∀ t, HasDerivAt f (f' t) t) {τ : ℝ}
    (hτ : τ ≠ 0) : ∃ ξ, ξ ≠ 0 ∧ |ξ| < |τ| ∧ (f τ - f 0) / τ = f' ξ := by
  have hcont : ∀ s, ContinuousAt f s := fun s => (hderiv s).continuousAt
  rcases lt_or_gt_of_ne hτ with hneg | hpos
  · obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope f f' hneg
      (fun s _ => (hcont s).continuousWithinAt) (fun s _ => hderiv s)
    refine ⟨ξ, hξ.2.ne, ?_, ?_⟩
    · rw [abs_of_neg hneg, abs_of_neg hξ.2]; linarith [hξ.1]
    · rw [hslope, zero_sub, div_neg, ← neg_div, neg_sub]
  · obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope f f' hpos
      (fun s _ => (hcont s).continuousWithinAt) (fun s _ => hderiv s)
    refine ⟨ξ, hξ.1.ne', ?_, ?_⟩
    · rw [abs_of_pos hpos, abs_of_pos hξ.1]; exact hξ.2
    · rw [hslope, sub_zero]

/-- Second-order Taylor with Lagrange remainder, from two mean value theorems:
f(τ) − f(0) − τf'(0) = τ²f''(ξ)/2 with |ξ| < |τ|. -/
theorem taylor2 {f f' f'' : ℝ → ℝ} (hf : ∀ t, HasDerivAt f (f' t) t)
    (hf' : ∀ t, HasDerivAt f' (f'' t) t) {τ : ℝ} (hτ : τ ≠ 0) :
    ∃ ξ, |ξ| < |τ| ∧ f τ - f 0 - τ * f' 0 = τ ^ 2 * f'' ξ / 2 := by
  set R : ℝ := f τ - f 0 - τ * f' 0 with hR
  -- g(t) := f(t) − f(0) − t·f'(0) − (t²/τ²)·R vanishes at 0 and τ
  set g : ℝ → ℝ := fun t => f t - f 0 - t * f' 0 - t ^ 2 / τ ^ 2 * R with hg
  set g' : ℝ → ℝ := fun t => f' t - f' 0 - 2 * t / τ ^ 2 * R with hg'
  have hgd : ∀ t, HasDerivAt g (g' t) t := fun t => by
    have h1 := ((hf t).sub_const (f 0)).sub ((hasDerivAt_id' t).mul_const (f' 0))
    have h2 := ((hasDerivAt_pow 2 t).div_const (τ ^ 2)).mul_const R
    have h3 := h1.sub h2
    refine h3.congr_deriv ?_
    simp only [hg']; push_cast; ring
  have hg0 : g 0 = 0 := by simp [hg]
  have hgτ : g τ = 0 := by
    simp only [hg, hR]
    have : τ ^ 2 / τ ^ 2 = 1 := div_self (pow_ne_zero 2 hτ)
    rw [this]; ring
  obtain ⟨ξ₁, hξ₁ne, hξ₁, hslope₁⟩ := slope_eq_strict hgd hτ
  rw [hgτ, hg0, sub_zero, zero_div] at hslope₁
  -- g'(ξ₁) = 0 : f'(ξ₁) − f'(0) = (2ξ₁/τ²)·R
  have hkey : f' ξ₁ - f' 0 = 2 * ξ₁ / τ ^ 2 * R := by
    have := hslope₁.symm; simp only [hg'] at this; linarith
  obtain ⟨ξ, hξ, hslope₂⟩ := Hadamard.entry_slope_eq hf' hξ₁ne
  refine ⟨ξ, lt_trans hξ hξ₁, ?_⟩
  -- (f'(ξ₁) − f'(0))/ξ₁ = f''(ξ) ⇒ f''(ξ) = 2R/τ²
  have h2 : f' ξ₁ - f' 0 = ξ₁ * f'' ξ := by rw [← hslope₂]; field_simp
  have hτ2 : τ ^ 2 ≠ 0 := pow_ne_zero 2 hτ
  have : ξ₁ * f'' ξ = 2 * ξ₁ / τ ^ 2 * R := by rw [← h2, hkey]
  have h3 : ξ₁ * (f'' ξ * τ ^ 2 - 2 * R) = 0 := by
    have h4 : ξ₁ * f'' ξ * τ ^ 2 = 2 * ξ₁ * R := by
      rw [this]; field_simp
    linear_combination h4
  rcases mul_eq_zero.mp h3 with h | h
  · exact absurd h hξ₁ne
  · linarith

theorem hasDerivAt_hq_of_ne {f f' f'' : ℝ → ℝ} (hf : ∀ t, HasDerivAt f (f' t) t) {τ : ℝ}
    (hτ : τ ≠ 0) : HasDerivAt (hq f f') (hq' f f' f'' τ) τ := by
  have h : HasDerivAt (fun t => (f t - f 0) / t) ((f' τ * τ - (f τ - f 0) * 1) / τ ^ 2) τ :=
    ((hf τ).sub_const (f 0)).div (hasDerivAt_id' τ) hτ
  have heq : hq f f' =ᶠ[𝓝 τ] fun t => (f t - f 0) / t := by
    filter_upwards [eventually_ne_nhds hτ] with t ht
    simp [hq, ht]
  refine (h.congr_of_eventuallyEq heq).congr_deriv ?_
  simp only [hq', hτ, if_false]; ring

theorem hasDerivAt_hq_zero {f f' f'' : ℝ → ℝ} (hf : ∀ t, HasDerivAt f (f' t) t)
    (hf' : ∀ t, HasDerivAt f' (f'' t) t) (hc : ContinuousAt f'' 0) :
    HasDerivAt (hq f f') (hq' f f' f'' 0) 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero, Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.mp hc ε hε
  refine ⟨δ, hδ, fun t ht hdist => ?_⟩
  have ht0 : t ≠ 0 := by simpa using ht
  obtain ⟨ξ, hξ, hR⟩ := taylor2 hf hf' ht0
  have hval : t⁻¹ • (hq f f' (0 + t) - hq f f' 0) = f'' ξ / 2 := by
    simp only [hq, zero_add, ht0, if_false, if_true, smul_eq_mul]
    have hft : f t - f 0 = t * f' 0 + t ^ 2 * f'' ξ / 2 := by linarith
    rw [hft]
    field_simp
    ring
  rw [hval]
  rw [Real.dist_eq, sub_zero] at hdist
  have hξδ : dist ξ 0 < δ := by rw [Real.dist_eq, sub_zero]; exact lt_trans hξ hdist
  have := hball hξδ
  rw [Real.dist_eq] at this
  simp only [hq', if_true]
  rw [Real.dist_eq]
  calc |f'' ξ / 2 - f'' 0 / 2| = |f'' ξ - f'' 0| / 2 := by rw [← sub_div, abs_div, abs_two]
    _ < ε := by linarith

theorem hasDerivAt_hq {f f' f'' : ℝ → ℝ} (hf : ∀ t, HasDerivAt f (f' t) t)
    (hf' : ∀ t, HasDerivAt f' (f'' t) t) (hc : ContinuousAt f'' 0) (τ : ℝ) :
    HasDerivAt (hq f f') (hq' f f' f'' τ) τ := by
  by_cases hτ : τ = 0
  · subst hτ; exact hasDerivAt_hq_zero hf hf' hc
  · exact hasDerivAt_hq_of_ne hf hτ

/-- Joint continuity at (0,0) of the derivative of the Hadamard quotient of a parametrised
family, from joint continuity of the second derivative. -/
theorem continuousAt_hq' {F F' F'' : ℝ → ℝ → ℝ}
    (hF : ∀ θ t, HasDerivAt (F θ) (F' θ t) t) (hF' : ∀ θ t, HasDerivAt (F' θ) (F'' θ t) t)
    (hc : ContinuousAt (fun q : ℝ × ℝ => F'' q.1 q.2) (0, 0)) :
    ContinuousAt (fun p : ℝ × ℝ => hq' (F p.1) (F' p.1) (F'' p.1) p.2) (0, 0) := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.mp hc (ε / 4) (by positivity)
  refine ⟨δ, hδ, fun p hp => ?_⟩
  obtain ⟨θ, τ⟩ := p
  have hp' : |θ| < δ ∧ |τ| < δ := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero, sub_zero, max_lt_iff] at hp
    exact hp
  have hnear : ∀ ξ, |ξ| < δ → |F'' θ ξ - F'' 0 0| < ε / 4 := fun ξ hξ => by
    have := hball (show dist ((θ, ξ) : ℝ × ℝ) (0, 0) < δ by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero, sub_zero]; exact max_lt hp'.1 hξ)
    rwa [Real.dist_eq] at this
  have h00 : hq' (F 0) (F' 0) (F'' 0) 0 = F'' 0 0 / 2 := by simp [hq']
  rw [Real.dist_eq, h00]
  by_cases hτ : τ = 0
  · subst hτ
    have h0 : hq' (F θ) (F' θ) (F'' θ) 0 = F'' θ 0 / 2 := by simp [hq']
    rw [h0]
    have := hnear 0 (by simpa using hδ)
    calc |F'' θ 0 / 2 - F'' 0 0 / 2| = |F'' θ 0 - F'' 0 0| / 2 := by
          rw [← sub_div, abs_div, abs_two]
      _ < ε := by linarith
  · have hne : hq' (F θ) (F' θ) (F'' θ) τ = (τ * F' θ τ - (F θ τ - F θ 0)) / τ ^ 2 := by
      simp [hq', hτ]
    rw [hne]
    obtain ⟨ξ, hξ, hR⟩ := taylor2 (hF θ) (hF' θ) hτ
    obtain ⟨η, hη, hslope⟩ := Hadamard.entry_slope_eq (hF' θ) hτ
    have h1 : F' θ τ = F' θ 0 + τ * F'' θ η := by rw [← hslope]; field_simp; ring
    have hF : F θ τ - F θ 0 = τ * F' θ 0 + τ ^ 2 * F'' θ ξ / 2 := by linarith
    have hval : (τ * F' θ τ - (F θ τ - F θ 0)) / τ ^ 2 = F'' θ η - F'' θ ξ / 2 := by
      have hτ2 : τ ^ 2 ≠ 0 := pow_ne_zero 2 hτ
      rw [h1, hF]
      field_simp
      ring
    rw [hval]
    have e1 := hnear η (lt_trans hη hp'.2)
    have e2 := hnear ξ (lt_trans hξ hp'.2)
    calc |F'' θ η - F'' θ ξ / 2 - F'' 0 0 / 2|
        = |(F'' θ η - F'' 0 0) - (F'' θ ξ - F'' 0 0) / 2| := by ring_nf
      _ ≤ |F'' θ η - F'' 0 0| + |(F'' θ ξ - F'' 0 0) / 2| := abs_sub _ _
      _ = |F'' θ η - F'' 0 0| + |F'' θ ξ - F'' 0 0| / 2 := by rw [abs_div, abs_two]
      _ < ε := by linarith

end HQuot

/-! ## §4 The ledger bundles and their derivation from joint C³ -/
namespace Ledger

/-- The degree-1 cluster matrix is C¹ in τ (entrywise) with ∂_τM jointly continuous at (0,0).
(Moved here from the statement file 9/10: now DERIVED, see `Derived.clusterC1_of_C3`.) -/
structure ClusterC1 (M M' : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ) : Prop where
  deriv : ∀ θ τ i j, HasDerivAt (fun t => M θ t i j) (M' θ τ i j) τ
  cont : ∀ i j, ContinuousAt (fun q : ℝ × ℝ => M' q.1 q.2 i j) (0, 0)

/-- a = tr N and b = det N (M − s*·1 = τ·N) are C¹ in τ with jointly continuous derivatives.
(Moved here 9/10: now DERIVED, see `Derived.traceDetC1_of_C3`.) -/
structure TraceDetC1 (M M' : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (sStar : ℝ → ℝ)
    (a' b' : ℝ → ℝ → ℝ) : Prop where
  deriv_a : ∀ θ τ, HasDerivAt (fun τ => (Hadamard.Ndiv M M' sStar θ τ).trace) (a' θ τ) τ
  deriv_b : ∀ θ τ, HasDerivAt (fun τ => (Hadamard.Ndiv M M' sStar θ τ).det) (b' θ τ) τ
  cont_a' : ContinuousAt (Function.uncurry a') (0, 0)
  cont_b' : ContinuousAt (Function.uncurry b') (0, 0)

/-- e₁ has a bounded mixed partial ∂_θ∂_τe₁ on the ε-square: joint C².
(Moved here 9/10: now DERIVED, see `Derived.pureSumC2_of_C3`.) -/
structure PureSumC2 (e₁ e₁τ e₁θτ : ℝ → ℝ → ℝ) (K₁ ε : ℝ) : Prop where
  K_pos : 0 < K₁
  ε_pos : 0 < ε
  deriv_τ : ∀ θ τ, HasDerivAt (e₁ θ) (e₁τ θ τ) τ
  deriv_θτ : ∀ θ τ, HasDerivAt (fun θ => e₁τ θ τ) (e₁θτ θ τ) θ
  bound : ∀ θ τ, |θ| < ε → |τ| < ε → |e₁θτ θ τ| ≤ K₁

/-- e₂ has ∂²_τe₂ with a bounded θ-derivative on the ε-square.
(Moved here 9/10: now DERIVED, see `Derived.pureProdC3_of_C3`.) -/
structure PureProdC3 (e₂ e₂τ e₂ττ e₂θττ : ℝ → ℝ → ℝ) (K₂ ε : ℝ) : Prop where
  K_pos : 0 < K₂
  deriv_τ : ∀ θ τ, HasDerivAt (e₂ θ) (e₂τ θ τ) τ
  deriv_ττ : ∀ θ τ, HasDerivAt (e₂τ θ) (e₂ττ θ τ) τ
  deriv_θττ : ∀ θ τ, HasDerivAt (fun θ => e₂ττ θ τ) (e₂θττ θ τ) θ
  bound : ∀ θ τ, |θ| < ε → |τ| < ε → |e₂θττ θ τ| ≤ K₂

/-- INPUT (B), all of it: the entries of the degree-1 (2×2) and degree-2 (4×4) cluster matrices
are jointly C³ in (θ,τ). Stated globally, like every `HasDerivAt` binder in the suite: the cluster
matrices are defined near (0,0), and a C³ function on a ball restricted to a smaller closed ball
extends to a C³ function on the plane. -/
structure ClusterC3 (M : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (A : ℝ → ℝ → Matrix (Fin 4) (Fin 4) ℝ) : Prop where
  deg1 : ∀ i j, ContDiff ℝ 3 fun q : ℝ × ℝ => M q.1 q.2 i j
  deg2 : ∀ i j, ContDiff ℝ 3 fun q : ℝ × ℝ => A q.1 q.2 i j

end Ledger

namespace Derived

open Regularity HQuot Hadamard ClusterMatrix Ledger

theorem finrank_resZero₁ (M : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (θ τ : ℝ) :
    Module.finrank ℝ (resZero₁ M θ τ) = (M θ τ).charpoly.rootMultiplicity 0 := by
  rw [resZero₁, LinearMap.finrank_maxGenEigenspace_eq, Matrix.charpoly_toLin']

theorem finrank_resZero₂ (A : ℝ → ℝ → Matrix (Fin 4) (Fin 4) ℝ) (θ τ : ℝ) :
    Module.finrank ℝ (resZero₂ A θ τ) = (A θ τ).charpoly.rootMultiplicity 0 := by
  rw [resZero₂, LinearMap.finrank_maxGenEigenspace_eq, Matrix.charpoly_toLin']

theorem two_add_one_le_three : (2 : WithTop ℕ∞) + 1 ≤ 3 := by norm_num
theorem one_add_one_le_two : (1 : WithTop ℕ∞) + 1 ≤ 2 := by norm_num
theorem zero_add_one_le_one : (0 : WithTop ℕ∞) + 1 ≤ 1 := by norm_num

variable {M : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ} {A : ℝ → ℝ → Matrix (Fin 4) (Fin 4) ℝ}
  {sStar : ℝ → ℝ}

theorem contDiff_Mτ (h : ClusterC3 M A) (i j : Fin 2) :
    ContDiff ℝ 2 fun q : ℝ × ℝ => Mτ M q.1 q.2 i j :=
  contDiff_pτ (f := fun θ τ => M θ τ i j) two_add_one_le_three (h.deg1 i j)

theorem contDiff_Mττ (h : ClusterC3 M A) (i j : Fin 2) :
    ContDiff ℝ 1 fun q : ℝ × ℝ => Mττ M q.1 q.2 i j :=
  contDiff_pτ (f := fun θ τ => Mτ M θ τ i j) one_add_one_le_two (contDiff_Mτ h i j)

theorem hasDerivAt_M (h : ClusterC3 M A) (θ τ : ℝ) (i j : Fin 2) :
    HasDerivAt (fun t => M θ t i j) (Mτ M θ τ i j) τ :=
  hasDerivAt_pτ (f := fun θ τ => M θ τ i j)
    (differentiable_of_contDiff (f := fun θ τ => M θ τ i j) two_add_one_le_three (h.deg1 i j)) θ τ

theorem hasDerivAt_Mτ (h : ClusterC3 M A) (θ τ : ℝ) (i j : Fin 2) :
    HasDerivAt (fun t => Mτ M θ t i j) (Mττ M θ τ i j) τ :=
  hasDerivAt_pτ (f := fun θ τ => Mτ M θ τ i j)
    (differentiable_of_contDiff (f := fun θ τ => Mτ M θ τ i j) one_add_one_le_two
      (contDiff_Mτ h i j)) θ τ

theorem continuousAt_Mττ (h : ClusterC3 M A) (i j : Fin 2) :
    ContinuousAt (fun q : ℝ × ℝ => Mττ M q.1 q.2 i j) (0, 0) :=
  (contDiff_Mττ h i j).continuous.continuousAt

/-- ClusterC3 ⇒ ClusterC1 with M' = ∂_τM. -/
theorem clusterC1_of_C3 (h : ClusterC3 M A) : ClusterC1 M (Mτ M) where
  deriv := hasDerivAt_M h
  cont i j := (contDiff_Mτ h i j).continuous.continuousAt

theorem Ndiv_eq_hq (hsemi : ∀ θ, M θ 0 = sStar θ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) (θ τ : ℝ)
    (i j : Fin 2) :
    Ndiv M (Mτ M) sStar θ τ i j = hq (fun t => M θ t i j) (fun t => Mτ M θ t i j) τ := by
  unfold Ndiv hq
  split_ifs with hτ
  · rfl
  · simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, hsemi θ]
    ring

theorem hasDerivAt_Ndiv_entry (h : ClusterC3 M A)
    (hsemi : ∀ θ, M θ 0 = sStar θ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) (θ τ : ℝ) (i j : Fin 2) :
    HasDerivAt (fun τ => Ndiv M (Mτ M) sStar θ τ i j) (Nτ M θ τ i j) τ := by
  have heq : (fun τ => Ndiv M (Mτ M) sStar θ τ i j) =
      hq (fun t => M θ t i j) (fun t => Mτ M θ t i j) := funext fun τ => Ndiv_eq_hq hsemi θ τ i j
  have hc : Continuous fun t => Mττ M θ t i j :=
    (contDiff_Mττ h i j).continuous.comp (continuous_const.prodMk continuous_id)
  rw [heq]
  exact hasDerivAt_hq (fun t => hasDerivAt_M h θ t i j) (fun t => hasDerivAt_Mτ h θ t i j)
    hc.continuousAt τ

theorem hasDerivAt_trace_Ndiv (h : ClusterC3 M A)
    (hsemi : ∀ θ, M θ 0 = sStar θ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) (θ τ : ℝ) :
    HasDerivAt (fun τ => (Ndiv M (Mτ M) sStar θ τ).trace) (aτ M θ τ) τ := by
  simp only [Matrix.trace_fin_two, aτ]
  exact (hasDerivAt_Ndiv_entry h hsemi θ τ 0 0).add (hasDerivAt_Ndiv_entry h hsemi θ τ 1 1)

theorem hasDerivAt_det_Ndiv (h : ClusterC3 M A)
    (hsemi : ∀ θ, M θ 0 = sStar θ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) (θ τ : ℝ) :
    HasDerivAt (fun τ => (Ndiv M (Mτ M) sStar θ τ).det) (bτ M sStar θ τ) τ := by
  simp only [Matrix.det_fin_two, bτ]
  exact ((hasDerivAt_Ndiv_entry h hsemi θ τ 0 0).mul (hasDerivAt_Ndiv_entry h hsemi θ τ 1 1)).sub
    ((hasDerivAt_Ndiv_entry h hsemi θ τ 0 1).mul (hasDerivAt_Ndiv_entry h hsemi θ τ 1 0))

theorem continuousAt_Nτ_entry (h : ClusterC3 M A) (i j : Fin 2) :
    ContinuousAt (fun q : ℝ × ℝ => Nτ M q.1 q.2 i j) (0, 0) :=
  continuousAt_hq' (F := fun θ t => M θ t i j) (F' := fun θ t => Mτ M θ t i j)
    (F'' := fun θ t => Mττ M θ t i j) (fun θ t => hasDerivAt_M h θ t i j)
    (fun θ t => hasDerivAt_Mτ h θ t i j) (continuousAt_Mττ h i j)

theorem continuousAt_aτ (h : ClusterC3 M A) : ContinuousAt (Function.uncurry (aτ M)) (0, 0) := by
  have : Function.uncurry (aτ M) = fun q : ℝ × ℝ => Nτ M q.1 q.2 0 0 + Nτ M q.1 q.2 1 1 := by
    funext q; simp [Function.uncurry, aτ, Matrix.trace_fin_two]
  rw [this]
  exact (continuousAt_Nτ_entry h 0 0).add (continuousAt_Nτ_entry h 1 1)

theorem continuousAt_bτ (h : ClusterC3 M A)
    (hsemi : ∀ θ, M θ 0 = sStar θ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) :
    ContinuousAt (Function.uncurry (bτ M sStar)) (0, 0) := by
  have hN := continuousAt_Ndiv_entry M (Mτ M) sStar hsemi (hasDerivAt_M h)
    (fun i j => (contDiff_Mτ h i j).continuous.continuousAt)
  have hNτ := continuousAt_Nτ_entry (M := M) h
  change ContinuousAt (fun q : ℝ × ℝ => bτ M sStar q.1 q.2) (0, 0)
  simp only [bτ]
  exact (((hNτ 0 0).mul (hN 1 1)).add ((hN 0 0).mul (hNτ 1 1))).sub
    (((hNτ 0 1).mul (hN 1 0)).add ((hN 0 1).mul (hNτ 1 0)))

/-- ClusterC3 (+ semisimplicity at τ = 0) ⇒ TraceDetC1 with the explicit derivatives. -/
theorem traceDetC1_of_C3 (h : ClusterC3 M A)
    (hsemi : ∀ θ, M θ 0 = sStar θ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) :
    TraceDetC1 M (Mτ M) sStar (aτ M) (bτ M sStar) where
  deriv_a := hasDerivAt_trace_Ndiv h hsemi
  deriv_b := hasDerivAt_det_Ndiv h hsemi
  cont_a' := continuousAt_aτ h
  cont_b' := continuousAt_bτ h hsemi

theorem contDiff_E₁f (h : ClusterC3 M A) : ContDiff ℝ 3 fun q : ℝ × ℝ => E₁f M A q.1 q.2 :=
  contDiff_E₁ (A := fun q : ℝ × ℝ => A q.1 q.2) (M := fun q : ℝ × ℝ => M q.1 q.2) h.deg2 h.deg1

theorem contDiff_E₂f (h : ClusterC3 M A) : ContDiff ℝ 3 fun q : ℝ × ℝ => E₂f M A q.1 q.2 :=
  contDiff_E₂ (A := fun q : ℝ × ℝ => A q.1 q.2) (M := fun q : ℝ × ℝ => M q.1 q.2) h.deg2 h.deg1

/-- ClusterC3 ⇒ PureSumC2 on the unit square, with the partials as the derivative data. -/
theorem pureSumC2_of_C3 (h : ClusterC3 M A) :
    ∃ K₁ : ℝ, PureSumC2 (E₁f M A) (pτ (E₁f M A)) (pθ (pτ (E₁f M A))) K₁ 1 := by
  have h3 := contDiff_E₁f h
  have h2 : ContDiff ℝ 2 fun q : ℝ × ℝ => pτ (E₁f M A) q.1 q.2 :=
    contDiff_pτ (f := E₁f M A) two_add_one_le_three h3
  have h1 : ContDiff ℝ 1 fun q : ℝ × ℝ => pθ (pτ (E₁f M A)) q.1 q.2 :=
    contDiff_pθ (f := pτ (E₁f M A)) one_add_one_le_two h2
  obtain ⟨K, hK, hb⟩ := bound_on_square h1.continuous
  exact ⟨K, hK, one_pos,
    hasDerivAt_pτ (f := E₁f M A) (differentiable_of_contDiff two_add_one_le_three h3),
    hasDerivAt_pθ (f := pτ (E₁f M A)) (differentiable_of_contDiff one_add_one_le_two h2), hb⟩

/-- ClusterC3 ⇒ PureProdC3 on the unit square. -/
theorem pureProdC3_of_C3 (h : ClusterC3 M A) :
    ∃ K₂ : ℝ, PureProdC3 (E₂f M A) (pτ (E₂f M A)) (pτ (pτ (E₂f M A)))
      (pθ (pτ (pτ (E₂f M A)))) K₂ 1 := by
  have h3 := contDiff_E₂f h
  have h2 : ContDiff ℝ 2 fun q : ℝ × ℝ => pτ (E₂f M A) q.1 q.2 :=
    contDiff_pτ (f := E₂f M A) two_add_one_le_three h3
  have h1 : ContDiff ℝ 1 fun q : ℝ × ℝ => pτ (pτ (E₂f M A)) q.1 q.2 :=
    contDiff_pτ (f := pτ (E₂f M A)) one_add_one_le_two h2
  have h0 : ContDiff ℝ 0 fun q : ℝ × ℝ => pθ (pτ (pτ (E₂f M A))) q.1 q.2 :=
    contDiff_pθ (f := pτ (pτ (E₂f M A))) zero_add_one_le_one h1
  obtain ⟨K, hK, hb⟩ := bound_on_square h0.continuous
  exact ⟨K, hK,
    hasDerivAt_pτ (f := E₂f M A) (differentiable_of_contDiff two_add_one_le_three h3),
    hasDerivAt_pτ (f := pτ (E₂f M A)) (differentiable_of_contDiff one_add_one_le_two h2),
    hasDerivAt_pθ (f := pτ (pτ (E₂f M A))) (differentiable_of_contDiff zero_add_one_le_one h1),
    hb⟩

end Derived

/-! ## §5 Spectral facts on the matrices: mirror, pinning, exactness dictionary -/
namespace Spectral

open ClusterMatrix

/-- spec A = {s, s, s, −s} ⇒ c₁ = 2s, c₂ = 0 (coefficient extraction at z = 0, ±1, 2). -/
theorem coeffs_of_mirror {A : Matrix (Fin 4) (Fin 4) ℝ} {s : ℝ}
    (h : ∀ z, A.charpoly.eval z = (z - s) ^ 3 * (z + s)) : c₁ A = 2 * s ∧ c₂ A = 0 := by
  have h0 := h 0
  have h1 := h 1
  have hm := h (-1)
  have h2 := h 2
  simp only [eval_charpoly_eq_quartic, PureZeros.quartic] at h0 h1 hm h2
  ring_nf at h0 h1 hm h2
  constructor <;> linarith

/-- spec A = {0, 0, 0, t} ⇒ c₁ = t, c₂ = 0. -/
theorem coeffs_of_pinned {A : Matrix (Fin 4) (Fin 4) ℝ} {t : ℝ}
    (h : ∀ z, A.charpoly.eval z = z ^ 3 * (z - t)) : c₁ A = t ∧ c₂ A = 0 := by
  have h0 := h 0
  have h1 := h 1
  have hm := h (-1)
  have h2 := h 2
  simp only [eval_charpoly_eq_quartic, PureZeros.quartic] at h0 h1 hm h2
  ring_nf at h0 h1 hm h2
  constructor <;> linarith

/-- MIRROR (input A) on the matrices: M(θ,0) = s*·1 and spec A(θ,0) = {s*,s*,s*,−s*} ⇒
e₁(θ,0) = 0, e₂(θ,0) = −s*². -/
theorem E₁_mirror {A : Matrix (Fin 4) (Fin 4) ℝ} {M : Matrix (Fin 2) (Fin 2) ℝ} {s : ℝ}
    (hM : M = s • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (hA : ∀ z, A.charpoly.eval z = (z - s) ^ 3 * (z + s)) : E₁ A M = 0 := by
  obtain ⟨h1, _⟩ := coeffs_of_mirror hA
  rw [E₁, h1, hM, trace_smul_one]; ring

theorem E₂_mirror {A : Matrix (Fin 4) (Fin 4) ℝ} {M : Matrix (Fin 2) (Fin 2) ℝ} {s : ℝ}
    (hM : M = s • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (hA : ∀ z, A.charpoly.eval z = (z - s) ^ 3 * (z + s)) : E₂ A M = -s ^ 2 := by
  obtain ⟨h1, h2⟩ := coeffs_of_mirror hA
  rw [E₂, E₁, h1, h2, hM, trace_smul_one, det_smul_one]; ring

/-- PINNING (input D) on the matrices: det M(0,τ) = 0 and spec A(0,τ) = {0,0,0,tr M(0,τ)} ⇒
e₁(0,τ) = 0, e₂(0,τ) = 0. -/
theorem E₁_pinned {A : Matrix (Fin 4) (Fin 4) ℝ} {M : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : ∀ z, A.charpoly.eval z = z ^ 3 * (z - M.trace)) : E₁ A M = 0 := by
  obtain ⟨h1, _⟩ := coeffs_of_pinned hA
  rw [E₁, h1]; ring

theorem E₂_pinned {A : Matrix (Fin 4) (Fin 4) ℝ} {M : Matrix (Fin 2) (Fin 2) ℝ}
    (hdet : M.det = 0) (hA : ∀ z, A.charpoly.eval z = z ^ 3 * (z - M.trace)) : E₂ A M = 0 := by
  obtain ⟨h1, h2⟩ := coeffs_of_pinned hA
  rw [E₂, E₁, h1, h2, hdet]; ring

/-- The pure quadratic as a polynomial. -/
noncomputable def Qpoly (e₁ e₂ : ℝ) : ℝ[X] := X ^ 2 - C e₁ * X + C e₂

theorem eval_Qpoly (e₁ e₂ z : ℝ) : (Qpoly e₁ e₂).eval z = z ^ 2 - e₁ * z + e₂ := by
  simp [Qpoly]

theorem Qpoly_ne_zero (e₁ e₂ : ℝ) : Qpoly e₁ e₂ ≠ 0 := by
  intro h
  have := congrArg (fun p : ℝ[X] => p.coeff 2) h
  simp [Qpoly] at this

/-- The 2×2 characteristic polynomial factors through its two eigenvalues. -/
theorem charpoly_fin_two_factor {M : Matrix (Fin 2) (Fin 2) ℝ} {scl snc : ℝ}
    (hs : scl + snc = M.trace) (hp : scl * snc = M.det) :
    M.charpoly = (X - C scl) * (X - C snc) := by
  apply Polynomial.funext
  intro z
  rw [eval_charpoly_fin_two, ← hs, ← hp]
  simp only [eval_mul, eval_sub, eval_X, eval_C]
  ring

/-- At a crossing (snc = 0, scl ≠ 0): 0 is a SIMPLE eigenvalue of the degree-1 cluster. -/
theorem rootMultiplicity_zero_fin_two {M : Matrix (Fin 2) (Fin 2) ℝ} {scl snc : ℝ}
    (hne : scl ≠ snc) (hsnc : snc = 0) (hs : scl + snc = M.trace) (hp : scl * snc = M.det) :
    M.charpoly.rootMultiplicity 0 = 1 := by
  have hscl : (0 : ℝ) ≠ scl := fun h => hne (h.symm.trans hsnc.symm)
  rw [charpoly_fin_two_factor hs hp, hsnc,
    rootMultiplicity_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)),
    rootMultiplicity_X_sub_C, rootMultiplicity_X_sub_C]
  simp [hscl]

/-- LOCKED BRANCHES: if the two degree-1 eigenvalues (distinct) are degree-2 eigenvalues, the
degree-2 characteristic polynomial factors as (X − s_cl)(X − s_nc)·Q with Q the pure quadratic of
E₁, E₂ (quartic division). -/
theorem charpoly_factor_locked {A : Matrix (Fin 4) (Fin 4) ℝ} {M : Matrix (Fin 2) (Fin 2) ℝ}
    {scl snc : ℝ} (hne : scl ≠ snc) (hs : scl + snc = M.trace) (hp : scl * snc = M.det)
    (hlocked : ∀ z, M.charpoly.eval z = 0 → A.charpoly.eval z = 0) :
    A.charpoly = (X - C scl) * (X - C snc) * Qpoly (E₁ A M) (E₂ A M) := by
  have hroot : ∀ w, w = scl ∨ w = snc → M.charpoly.eval w = 0 := by
    rintro w (rfl | rfl) <;> rw [eval_charpoly_fin_two, ← hs, ← hp] <;> ring
  have h1 : PureZeros.quartic (c₁ A) (c₂ A) (c₃ A) (c₄ A) scl = 0 := by
    rw [← eval_charpoly_eq_quartic]; exact hlocked _ (hroot _ (Or.inl rfl))
  have h2 : PureZeros.quartic (c₁ A) (c₂ A) (c₃ A) (c₄ A) snc = 0 := by
    rw [← eval_charpoly_eq_quartic]; exact hlocked _ (hroot _ (Or.inr rfl))
  apply Polynomial.funext
  intro z
  rw [eval_charpoly_eq_quartic, PureZeros.quartic_factor hne h1 h2]
  simp only [Qpoly, eval_mul, eval_sub, eval_add, eval_pow, eval_X, eval_C]
  rw [E₁_eq A M hs, E₂_eq A M hs hp]

theorem rootMultiplicity_zero_locked {scl : ℝ} (hscl : scl ≠ 0) (e₁ e₂ : ℝ) :
    ((X - C scl) * (X - C (0 : ℝ)) * Qpoly e₁ e₂).rootMultiplicity 0 =
      1 + (Qpoly e₁ e₂).rootMultiplicity 0 := by
  have hQ := Qpoly_ne_zero e₁ e₂
  have h12 : (X - C scl) * (X - C (0 : ℝ)) ≠ 0 :=
    mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)
  rw [rootMultiplicity_mul (mul_ne_zero h12 hQ), rootMultiplicity_mul h12,
    rootMultiplicity_X_sub_C, rootMultiplicity_X_sub_C]
  simp [Ne.symm hscl]

/-- THE EXACTNESS DICTIONARY. At a crossing (s_nc = 0 ≠ s_cl, locked branches in degree 2): if
the algebraic multiplicity of 0 in the degree-2 cluster is 2 (= 2·c₁ by exactness), then the pure
quadratic has 0 as a SIMPLE root: e₂ = 0 and e₁ ≠ 0 — the former `hexactZero` and `hgeneric`. -/
theorem crossing_pure_data {A : Matrix (Fin 4) (Fin 4) ℝ} {M : Matrix (Fin 2) (Fin 2) ℝ}
    {scl snc : ℝ} (hne : scl ≠ snc) (hsnc : snc = 0) (hs : scl + snc = M.trace)
    (hp : scl * snc = M.det) (hlocked : ∀ z, M.charpoly.eval z = 0 → A.charpoly.eval z = 0)
    (hmult : A.charpoly.rootMultiplicity 0 = 2) : E₂ A M = 0 ∧ E₁ A M ≠ 0 := by
  have hscl : scl ≠ 0 := fun h => hne (h.trans hsnc.symm)
  have hfac := charpoly_factor_locked hne hs hp hlocked
  rw [hfac, hsnc, rootMultiplicity_zero_locked hscl] at hmult
  have hQ1 : (Qpoly (E₁ A M) (E₂ A M)).rootMultiplicity 0 = 1 := by omega
  have hroot : (Qpoly (E₁ A M) (E₂ A M)).IsRoot 0 :=
    (rootMultiplicity_pos (Qpoly_ne_zero _ _)).mp (by omega)
  have hE₂ : E₂ A M = 0 := by
    have := IsRoot.def.mp hroot
    rw [eval_Qpoly] at this
    simpa using this
  refine ⟨hE₂, fun hE₁ => ?_⟩
  have hQX : Qpoly (E₁ A M) (E₂ A M) = (X - C (0 : ℝ)) ^ 2 := by
    rw [hE₁, hE₂]; simp [Qpoly]
  rw [hQX, rootMultiplicity_X_sub_C_pow] at hQ1
  omega

end Spectral

/-! ## §8 (9/14) `hsemisimple` from its inputs: two independent states at s* in a rank-2 cluster -/
namespace Derived

/-- SATURATION, matrix form. Two linearly independent eigenvectors of a real 2×2 matrix with the same
eigenvalue s force the matrix to be s·1: the rank (2, the type) plus two independent resonant states
at s*(θ) — d₀f and I·d₀f (rederivation A2) — give M(θ,0) = s*(θ)·1, the former binder `hsemisimple`.
Wraps `Saturation.scalar_of_two_eigenvectors` (rate file §6) through `Matrix.toLin'`. -/
theorem matrix_scalar_of_two_eigenvectors (M : Matrix (Fin 2) (Fin 2) ℝ) (s : ℝ)
    (v₁ v₂ : Fin 2 → ℝ) (hind : LinearIndependent ℝ ![v₁, v₂])
    (h₁ : M *ᵥ v₁ = s • v₁) (h₂ : M *ᵥ v₂ = s • v₂) :
    M = s • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  have hT : Matrix.toLin' M = s • LinearMap.id :=
    Saturation.scalar_of_two_eigenvectors (K := ℝ) (V := Fin 2 → ℝ) (Module.finrank_fin_fun ℝ)
      (Matrix.toLin' M) s v₁ v₂ hind (by rw [Matrix.toLin'_apply]; exact h₁)
      (by rw [Matrix.toLin'_apply]; exact h₂)
  refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
  have hv := congrArg (fun T : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) => T v) hT
  simp only [LinearMap.smul_apply, LinearMap.id_apply] at hv
  rw [hv, Matrix.toLin'_apply]
  ext i
  fin_cases i <;> simp

/-- The ledger shape: for every θ, two independent states at s*(θ) in the degree-1 cluster at g_hyp
⇒ M(θ,0) = s*(θ)·1. -/
theorem semisimple_of_states (M : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (sStar : ℝ → ℝ)
    (hstates : ∀ θ, ∃ v₁ v₂ : Fin 2 → ℝ, LinearIndependent ℝ ![v₁, v₂] ∧
      M θ 0 *ᵥ v₁ = sStar θ • v₁ ∧ M θ 0 *ᵥ v₂ = sStar θ • v₂) :
    ∀ θ, M θ 0 = sStar θ • (1 : Matrix (Fin 2) (Fin 2) ℝ) := fun θ => by
  obtain ⟨v₁, v₂, hind, h₁, h₂⟩ := hstates θ
  exact matrix_scalar_of_two_eigenvectors _ _ _ _ hind h₁ h₂

end Derived

/-! ## §7 (9/11) The pure-zero branch DEFINED: the root of Q nearest 0 -/
namespace Branch

open TwinRate PureZeros

theorem wMinus_root {a b : ℝ} (hD : 0 ≤ disc a b) : wMinus a b ^ 2 - a * wMinus a b + b = 0 := by
  have h := Real.sq_sqrt hD
  unfold disc at h; unfold wMinus disc; linear_combination h / 4

/-- Wherever the discriminant is nonnegative, `zBranch` is a root of Q. -/
theorem zBranch_root (e₁ e₂ : ℝ → ℝ) (τ : ℝ) (hD : 0 ≤ disc (e₁ τ) (e₂ τ)) :
    zBranch e₁ e₂ τ ^ 2 - e₁ τ * zBranch e₁ e₂ τ + e₂ τ = 0 := by
  unfold zBranch
  split_ifs
  · exact wPlus_root hD
  · exact wMinus_root hD

/-- At a point where Q has the SIMPLE root 0 (e₂ = 0, e₁ ≠ 0) and e₁, e₂ are continuous, the
nearest-zero branch vanishes and is continuous — the former `hbranch`. -/
theorem zBranch_at_simple_zero {e₁ e₂ : ℝ → ℝ} {σ : ℝ} (hc₁ : ContinuousAt e₁ σ)
    (hc₂ : ContinuousAt e₂ σ) (h₂ : e₂ σ = 0) (h₁ : e₁ σ ≠ 0) :
    ContinuousAt (zBranch e₁ e₂) σ ∧ zBranch e₁ e₂ σ = 0 := by
  have hpair : ContinuousAt (fun τ => (e₁ τ, e₂ τ)) σ := hc₁.prodMk hc₂
  have hwP : ContinuousAt (fun τ => wPlus (e₁ τ) (e₂ τ)) σ := (continuousAt_wPlus _).comp hpair
  have hwM : ContinuousAt (fun τ => wMinus (e₁ τ) (e₂ τ)) σ := (continuousAt_wMinus _).comp hpair
  have habsP : ContinuousAt (fun τ => |wPlus (e₁ τ) (e₂ τ)|) σ :=
    continuous_abs.continuousAt.comp hwP
  have habsM : ContinuousAt (fun τ => |wMinus (e₁ τ) (e₂ τ)|) σ :=
    continuous_abs.continuousAt.comp hwM
  have hhalf : 0 < |e₁ σ| / 2 := by have := abs_pos.mpr h₁; linarith
  rcases lt_or_gt_of_ne h₁ with hneg | hpos
  · -- e₁(σ) < 0: w₊(σ) = 0 is the branch through 0, w₋(σ) = e₁(σ)
    have hPσ : wPlus (e₁ σ) (e₂ σ) = 0 := by rw [h₂]; exact wPlus_at_zero_neg hneg
    have hMσ : wMinus (e₁ σ) (e₂ σ) = e₁ σ := by rw [h₂]; exact wMinus_at_zero_neg hneg
    have h1 : ∀ᶠ τ in 𝓝 σ, |wPlus (e₁ τ) (e₂ τ)| < |e₁ σ| / 2 :=
      habsP.eventually (gt_mem_nhds (by
        change |wPlus (e₁ σ) (e₂ σ)| < _; rw [hPσ, abs_zero]; exact hhalf))
    have h2 : ∀ᶠ τ in 𝓝 σ, |e₁ σ| / 2 < |wMinus (e₁ τ) (e₂ τ)| :=
      habsM.eventually (lt_mem_nhds (by
        change _ < |wMinus (e₁ σ) (e₂ σ)|; rw [hMσ]; linarith))
    have heq : (fun τ => wPlus (e₁ τ) (e₂ τ)) =ᶠ[𝓝 σ] zBranch e₁ e₂ := by
      filter_upwards [h1, h2] with τ hτ1 hτ2
      simp only [zBranch]; rw [if_pos (le_of_lt (lt_trans hτ1 hτ2))]
    refine ⟨hwP.congr heq, ?_⟩
    simp only [zBranch]
    rw [if_pos (by rw [hPσ, abs_zero]; exact abs_nonneg _), hPσ]
  · -- e₁(σ) > 0: w₋(σ) = 0 is the branch through 0, w₊(σ) = e₁(σ)
    have hPσ : wPlus (e₁ σ) (e₂ σ) = e₁ σ := by rw [h₂]; exact wPlus_at_zero_pos hpos
    have hMσ : wMinus (e₁ σ) (e₂ σ) = 0 := by rw [h₂]; exact wMinus_at_zero_nonneg hpos.le
    have h1 : ∀ᶠ τ in 𝓝 σ, |wMinus (e₁ τ) (e₂ τ)| < |e₁ σ| / 2 :=
      habsM.eventually (gt_mem_nhds (by
        change |wMinus (e₁ σ) (e₂ σ)| < _; rw [hMσ, abs_zero]; exact hhalf))
    have h2 : ∀ᶠ τ in 𝓝 σ, |e₁ σ| / 2 < |wPlus (e₁ τ) (e₂ τ)| :=
      habsP.eventually (lt_mem_nhds (by
        change _ < |wPlus (e₁ σ) (e₂ σ)|; rw [hPσ]; linarith))
    have heq : (fun τ => wMinus (e₁ τ) (e₂ τ)) =ᶠ[𝓝 σ] zBranch e₁ e₂ := by
      filter_upwards [h1, h2] with τ hτ1 hτ2
      simp only [zBranch]; rw [if_neg (not_le.mpr (lt_trans hτ1 hτ2))]
    refine ⟨hwM.congr heq, ?_⟩
    simp only [zBranch]
    rw [if_neg (by rw [hPσ, hMσ, abs_zero]; exact not_le.mpr (abs_pos.mpr h₁)), hMσ]

end Branch

/-! ## §6 Capstone: Fried fails at the crossing, from the cluster matrices -/
namespace Capstone

open TwinRate Hadamard FirstVariation Derived Spectral ClusterMatrix Ledger OrderCount TorsionCore
  Regularity Branch

/-- FRIED FAILS AT THE CROSSING — THE MATRICES AS PRIMITIVES. Compared with
`fried_fails_at_crossing_of_pure_zero_inputs`: the four regularity bundles are replaced by
`ClusterC3` (joint C³ of the two cluster matrices); mirror and pinning are stated as spectra of the
degree-2 matrix; the locked branches enter as `hlocked` (degree-1 eigenvalues recur in degree 2);
`hexactZero` and `hgeneric` are DERIVED from exactness through the dictionary `hriesz`
(c_k = algebraic multiplicity of 0 in the degree-k cluster matrix). e₁, e₂, ∂_τM, a', b' are all
DEFINED from M and A; ⚡9/11: so is the pure-zero branch z = `Branch.zBranch` (root of Q nearest 0),
which removes the former `hzQ` and `hbranch`; and the ζ-side enters as the two facts it really is —
`ZetaFactorization` (CD (6.5) at λ = 0, with ζ₀(τ) = ζ(0; g_τ) and F its regular factor) and
`hfried_off` = "ζ₀ = τ_R off the crossing" (DGRS Thm 2 + Fried at g_hyp).
Conclusion: ζ₀(σ) ≠ τ_R. -/
theorem fried_fails_at_crossing_of_matrix_inputs
    {V₃ : Type*} [AddCommGroup V₃] [Module ℝ V₃]
    (M : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (A : ℝ → ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (sStar : ℝ → ℝ) (Bcc Bcψ Bψc Bψψ p : ℝ)
    (hsemisimple : ∀ θ, M θ 0 = sStar θ • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (hC3 : ClusterC3 M A)
    (hdet : Bcc * Bψψ - Bcψ * Bψc ≠ 0)
    (h422 : Bmat Bcc Bcψ Bψc Bψψ * Mτ M 0 0 = Pmat p)
    (hr₀ : 0 < Bcc * p / (Bcc * Bψψ - Bcψ * Bψc))
    (hsStar0 : sStar 0 = 0) (hsStarc : ContinuousAt sStar 0)
    (hsStarneg : ∀ θ, θ ≠ 0 → sStar θ < 0)
    (hmirror : ∀ θ z, (A θ 0).charpoly.eval z = (z - sStar θ) ^ 3 * (z + sStar θ))
    (hpinned : Pinned M A)
    (hlocked : ∀ θ τ z, (M θ τ).charpoly.eval z = 0 → (A θ τ).charpoly.eval z = 0) :
    let a : ℝ → ℝ → ℝ := fun θ τ => (Ndiv M (Mτ M) sStar θ τ).trace
    let b : ℝ → ℝ → ℝ := fun θ τ => (Ndiv M (Mτ M) sStar θ τ).det
    let a' : ℝ → ℝ → ℝ := aτ M
    let b' : ℝ → ℝ → ℝ := bτ M sStar
    let e₁ : ℝ → ℝ → ℝ := E₁f M A
    let e₂ : ℝ → ℝ → ℝ := E₂f M A
    let e₂τ : ℝ → ℝ → ℝ := pτ e₂
    let z : ℝ → ℝ → ℝ := fun θ => zBranch (e₁ θ) (e₂ θ)
    let r₀ : ℝ := Bcc * p / (Bcc * Bψψ - Bcψ * Bψc)
    ∃ K₁ : ℝ, 0 < K₁ ∧ ∃ θ₀ δ : ℝ, 0 < θ₀ ∧ 0 < δ ∧ ∀ θ, θ ≠ 0 → |θ| < θ₀ →
      ∀ (ζ₀ F : ℝ → ℝ) (c : Fin 5 → ℕ) (τR : ℝ),
        τR ≠ 0 →
        ZetaFactorization ζ₀ F (twin sStar a b θ) (z θ) δ →
        (∀ τ, |τ| < δ → twin sStar a b θ τ ≠ 0 → ζ₀ τ = τR) →
        (∀ τ₀, |τ₀| < δ → twin sStar a b θ τ₀ = 0 →
          ∃ (f : resZero₁ M θ τ₀ →ₗ[ℝ] resZero₂ A θ τ₀) (g : resZero₂ A θ τ₀ →ₗ[ℝ] V₃),
            Function.Injective f ∧ LinearMap.range f = LinearMap.ker g ∧ Function.Surjective g) →
        (c 0 = 0 ∧ c 4 = 0) → c 3 = c 1 →
        (∀ τ₀, |τ₀| < δ → twin sStar a b θ τ₀ = 0 →
          c 1 = Module.finrank ℝ (resZero₁ M θ τ₀) ∧ c 2 = Module.finrank ℝ (resZero₂ A θ τ₀) ∧
          c 3 = Module.finrank ℝ V₃) →
        ∃ σ, 0 < σ ∧ σ ≤ 2 * |sStar θ| / r₀ ∧ σ < δ ∧ twin sStar a b θ σ = 0 ∧
          (∀ τ, |τ| < δ → twin sStar a b θ τ = 0 → τ = σ) ∧
          zetaOrder c = 0 ∧
          HasDerivAt (z θ) (e₂τ θ σ / e₁ θ σ) σ ∧ 2 * r₀ < |e₂τ θ σ / e₁ θ σ| ∧
          |e₁ θ σ| ≤ K₁ * |θ| * σ ∧
          ∃ α ratio : ℝ, α ≠ 0 ∧ dtwin (a θ σ) (b θ σ) (a' θ σ) (b' θ σ) σ ≠ 0 ∧
            Tendsto (fun τ => twin sStar a b θ τ / z θ τ) (𝓝[≠] σ) (𝓝 ratio) ∧
            ratio = dtwin (a θ σ) (b θ σ) (a' θ σ) (b' θ σ) σ / α ∧ ratio ≠ 1 ∧
            ζ₀ σ = τR * ratio ∧ ζ₀ σ ≠ τR ∧
            refinedTorsion 1 (dtwin (a θ σ) (b θ σ) (a' θ σ) (b' θ σ) σ /
              (α - dtwin (a θ σ) (b θ σ) (a' θ σ) (b' θ σ) σ)) =
              -(α / dtwin (a θ σ) (b θ σ) (a' θ σ) (b' θ σ) σ) := by
  intro a b a' b' e₁ e₂ e₂τ z r₀
  -- the derived bundles
  have hC1 := clusterC1_of_C3 hC3
  have hTD := traceDetC1_of_C3 hC3 hsemisimple
  obtain ⟨K₁, hS⟩ := pureSumC2_of_C3 hC3
  obtain ⟨K₂, hP⟩ := pureProdC3_of_C3 hC3
  -- (4.22) pins a(0,0) = r₀, b(0,0) = 0
  have hM00 : Mτ M 0 0 = Nmat Bcc Bcψ Bψc Bψψ p := Nmat_unique hdet _ h422
  have ha0 : a 0 0 = r₀ := by
    change (Ndiv M (Mτ M) sStar 0 0).trace = _
    rw [Ndiv_zero, hM00, trace_Nmat]
  have hb0 : b 0 0 = 0 := by
    change (Ndiv M (Mτ M) sStar 0 0).det = 0
    rw [Ndiv_zero, hM00, det_Nmat]
  have hcont_a : ContinuousAt (Function.uncurry a) (0, 0) :=
    continuousAt_trace_Ndiv M (Mτ M) sStar hsemisimple hC1.deriv hC1.cont
  have hcont_b : ContinuousAt (Function.uncurry b) (0, 0) :=
    continuousAt_det_Ndiv M (Mτ M) sStar hsemisimple hC1.deriv hC1.cont
  -- the rate lemma: positive discriminant on an ε₁-square
  obtain ⟨ε₁, hε₁, hrate⟩ := twin_rate_of_cluster sStar a b a' b' hr₀ hTD.deriv_a hTD.deriv_b
    hcont_a hcont_b hTD.cont_a' hTD.cont_b' ha0 hb0
  -- mirror and pinning values
  have h₁τ0 : ∀ θ, e₁ θ 0 = 0 := fun θ => E₁_mirror (hsemisimple θ) (hmirror θ)
  have h₂τ0 : ∀ θ, e₂ θ 0 = -(sStar θ) ^ 2 := fun θ => E₂_mirror (hsemisimple θ) (hmirror θ)
  have h₁θ0 : ∀ τ, e₁ 0 τ = 0 := fun τ => E₁_pinned (hpinned.deg2 τ)
  have h₂θ0 : ∀ τ, e₂ 0 τ = 0 := fun τ => E₂_pinned (hpinned.deg1 τ) (hpinned.deg2 τ)
  -- the square: ε := min 1 ε₁ (bounds hold on the unit square, discriminant on the ε₁-square)
  have hε : 0 < min 1 ε₁ := lt_min one_pos hε₁
  obtain ⟨θ₀, δ, hθ₀, hδ, hθ₀ε, hδε, H⟩ :=
    fried_fails_at_crossing_of_pure_zero_inputs_ord
      sStar a b a' b' hr₀ hTD.deriv_a hTD.deriv_b hcont_a hcont_b hTD.cont_a' hTD.cont_b' ha0 hb0
      hsStar0 hsStarc hsStarneg e₁ e₂ (pτ e₁) (pθ (pτ e₁)) (pτ e₂) (pτ (pτ e₂))
      (pθ (pτ (pτ e₂))) hS.K_pos hP.K_pos hε hS.deriv_τ hS.deriv_θτ
      (fun θ τ hθ hτ => hS.bound θ τ (lt_of_lt_of_le hθ (min_le_left _ _))
        (lt_of_lt_of_le hτ (min_le_left _ _)))
      hP.deriv_τ hP.deriv_ττ hP.deriv_θττ
      (fun θ τ hθ hτ => hP.bound θ τ (lt_of_lt_of_le hθ (min_le_left _ _))
        (lt_of_lt_of_le hτ (min_le_left _ _)))
      h₁τ0 h₁θ0 h₂τ0 h₂θ0
  refine ⟨K₁, hS.K_pos, θ₀, δ, hθ₀, hδ, fun θ hθne hθ ζ₀ F c τR hτR hCD
    hfried_off hexact hacyc hdual hdims => ?_⟩
  have hθε₁ : |θ| < ε₁ := lt_of_lt_of_le hθ (le_trans hθ₀ε (min_le_right _ _))
  -- the exactness dictionary at each crossing: e₂ = 0, e₁ ≠ 0
  have hzc : ∀ τ₀, |τ₀| < δ → twin sStar a b θ τ₀ = 0 →
      ContinuousAt (z θ) τ₀ ∧ z θ τ₀ = 0 ∧ e₂ θ τ₀ = 0 ∧ e₁ θ τ₀ ≠ 0 := by
    intro τ₀ hτ₀ h0
    have hτ₀ε₁ : |τ₀| < ε₁ := lt_of_lt_of_le hτ₀ (le_trans hδε (min_le_right _ _))
    have hdisc : 0 < disc (a θ τ₀) (b θ τ₀) := (hrate θ τ₀ hθε₁ hτ₀ε₁).1
    have hτ₀ne : τ₀ ≠ 0 := by
      rintro rfl
      rw [twin_zero] at h0
      exact (hsStarneg θ hθne).ne h0
    -- the locked branches: s_cl = s* + τ₀w₋, s_nc = twin = s* + τ₀w₊
    have hsnc : twin sStar a b θ τ₀ = sStar θ + τ₀ * wPlus (a θ τ₀) (b θ τ₀) := rfl
    have hne : sStar θ + τ₀ * wMinus (a θ τ₀) (b θ τ₀) ≠ twin sStar a b θ τ₀ := by
      rw [hsnc]; exact (branches_ne hτ₀ne hdisc).symm
    have hMτ : M θ τ₀ = sStar θ • (1 : Matrix (Fin 2) (Fin 2) ℝ) + τ₀ • Ndiv M (Mτ M) sStar θ τ₀ :=
      M_eq M (Mτ M) sStar hsemisimple θ τ₀
    have hs : (sStar θ + τ₀ * wMinus (a θ τ₀) (b θ τ₀)) + twin sStar a b θ τ₀ =
        (M θ τ₀).trace := by
      rw [hsnc, hMτ, trace_M, clusterTrace]
      have := wPlus_add_wMinus (a θ τ₀) (b θ τ₀)
      change _ = 2 * sStar θ + τ₀ * a θ τ₀
      linear_combination τ₀ * this
    have hp : (sStar θ + τ₀ * wMinus (a θ τ₀) (b θ τ₀)) * twin sStar a b θ τ₀ =
        (M θ τ₀).det := by
      rw [hsnc, hMτ, det_M, clusterDet]
      have h1 := wPlus_add_wMinus (a θ τ₀) (b θ τ₀)
      have h2 := wPlus_mul_wMinus hdisc.le
      change _ = sStar θ ^ 2 + sStar θ * τ₀ * a θ τ₀ + τ₀ ^ 2 * b θ τ₀
      linear_combination (sStar θ * τ₀) * h1 + τ₀ ^ 2 * h2
    -- c₁ = 1, hence c₂ = 2 by exactness (dimensions = multiplicities: Mathlib)
    obtain ⟨hc1, hc2, hc3⟩ := hdims τ₀ hτ₀ h0
    have hf1 := finrank_resZero₁ M θ τ₀
    have hf2 := finrank_resZero₂ A θ τ₀
    have hc1' : c 1 = 1 := by
      rw [hc1, hf1]; exact rootMultiplicity_zero_fin_two hne h0 hs hp
    obtain ⟨f, g, hf, hfg, hg⟩ := hexact τ₀ hτ₀ h0
    have hmid := finrank_middle_of_exact f g hf hfg hg
    have hc2' : (A θ τ₀).charpoly.rootMultiplicity 0 = 2 := by omega
    obtain ⟨hE₂, hE₁⟩ := crossing_pure_data hne h0 hs hp (hlocked θ τ₀) hc2'
    -- the defined branch is continuous through 0 there
    obtain ⟨hzc, hz0⟩ := zBranch_at_simple_zero (e₁ := e₁ θ) (e₂ := e₂ θ)
      (hS.deriv_τ θ τ₀).continuousAt (hP.deriv_τ θ τ₀).continuousAt hE₂ hE₁
    exact ⟨hzc, hz0, hE₂, hE₁⟩
  -- the ζ-order at each crossing, from exactness
  have hord : ∀ τ₀, |τ₀| < δ → twin sStar a b θ τ₀ = 0 → zetaOrder c = 0 := by
    intro τ₀ hτ₀ h0
    obtain ⟨f, g, hf, hfg, hg⟩ := hexact τ₀ hτ₀ h0
    exact order_zero_of_exact f g hf hfg hg c hacyc hdual (hdims τ₀ hτ₀ h0)
  -- CD (6.5) off the crossing + DGRS constancy ⇒ the old `hfried_off` shape for F
  have hfo : ∀ τ, |τ| < δ → twin sStar a b θ τ ≠ 0 → F τ * z θ τ / twin sStar a b θ τ = τR :=
    fun τ hτ hne => by rw [← hCD.off τ hτ hne]; exact hfried_off τ hτ hne
  obtain ⟨σ, h1, h2, h3, h4, h5, h6, h7, h8, h9, α, ratio, hα, hb, hlim, hreq, hr1, hval, hne,
      htors⟩ :=
    H θ hθne hθ (z θ) F c τR hτR (fun τ hD => zBranch_root (e₁ θ) (e₂ θ) τ hD) hzc hCD.cont hfo
      hord
  refine ⟨σ, h1, h2, h3, h4, h5, h6, h7, h8, h9, α, ratio, hα, hb, hlim, hreq, hr1, ?_, ?_, htors⟩
  · rw [hCD.at_crossing σ h4]; exact hval
  · rw [hCD.at_crossing σ h4]; exact hne

end Capstone

end FriedCrossing
