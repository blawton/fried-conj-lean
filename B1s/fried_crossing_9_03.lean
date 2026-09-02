/-
FRIED AT A CODIMENSION-ONE CROSSING — THE LEDGER (9/03; vault memos
crossing_construction_rederivation_9_03 [cleanest statement], crossing_rate_ratio_9_03
[rate computation], jordan_cluster_torsion_9_03 [Lemma A], zero_cluster_torsion_9_02
[order m = dim C₀² − 2 dim C₀¹, cluster torsions]).

Claim ledgered: on a closed hyperbolic 3-manifold with b₁ = 1, acyclic χ_θ, along the
family g_τ = e^{−2τb}g_hyp the non-closed degree-1 resonance s_nc(θ,τ) crosses 0 at
τ = σ(θ). There ζ_{χ_θ}(·; g_σ) is REGULAR at 0 (order c₂ − 2c₁ = 0) but its value
jumps: ζ(0; g_σ) = τ_R · lim (pole rate / zero rate) ≠ τ_R. Classical Fried fails at
the crossing metric; CD's refined identity absorbs the defect into τ(C^•(0), Γ_ϑ),
whose value is −(zero rate)/(pole rate) (Lemma A, memo 9/03).

House method: analytic inputs are named, citation-shaped HYPOTHESES; everything
downstream is proved. ⚡AUDIT CRITERION: ZERO axioms of its own — `#print axioms` on
every theorem below (P1–P5) lists only Lean built-ins.

  P1 TorsionCore  — finite-dimensional refined torsion of the minimal zero clusters,
                    computed from explicit matrices (CD Def 3.2 basis-change
                    determinants, normalisation of zero_cluster_torsion_9_02 §2):
                    semisimple (1,2,1) cluster ⇒ −1; Jordan J₂ cluster ⇒ −(1+λ)/λ;
                    with λ = s_p/(s_z − s_p) this is −s_z/s_p (Lemma A shape).
  P2 OrderCount   — exact reduced complex C₀¹ → C₀² → C₀³ plus ⋆-duality c₃ = c₁ and
                    acyclicity c₀ = c₄ = 0 ⇒ c₂ = 2c₁, so the CD (5.9) order
                    Σ(−1)^k c_k vanishes (rank–nullity only).
  P3 Crossing     — IVT + monotonicity: a C¹ real branch with s(0) < 0 and
                    ∂_τ s ≥ r₀ > 0 crosses 0 exactly once, at σ ≤ |s(0)|/r₀.
  P4 RateRatio    — z ~ a(τ−σ), p ~ b(τ−σ) ⇒ z/p → a/b; if R·z/p ≡ τ_R off σ and R is
                    continuous at σ then R(σ) = τ_R·(b/a), ≠ τ_R iff a ≠ b.
  P5 Capstone     — `fried_fails_at_crossing_of_inputs` composes P1–P4 from the named
                    analytic inputs (hdouble, hsym, hrate_nonclosed, hrate_zero, hcont,
                    hfried_off, hexact, hacyc, hdual; bookkeeping hdims, hτR).
-/
import Mathlib

set_option linter.style.header false

namespace FriedCrossing

open Filter Topology Matrix

/-! ## §1 (P1) Finite-dimensional torsion core

Conventions (zero_cluster_torsion_9_02 §1–2): the zero cluster at the crossing has
C₀¹ = ⟨u⟩, C₀² = ⟨w₁, w₂⟩, C₀³ = ⟨Lu⟩ (L = ∧dα), and the full resonant complex is
C^k = α∧C₀^{k−1} ⊕ C₀^k with d(α∧v + w) = α∧(Xw − d₀v) + (d₀w + Lv). Bases:
C¹ = (u), C² = (α∧u, w₁, w₂), C³ = (α∧w₁, α∧w₂, Lu), C⁴ = (α∧Lu). The two minimal
shapes are one family: d₀u = w₁, Xw₂ = x·w₁, d₀w₂ = l·Lu — x = 0 is the semisimple
cluster (D), x = 1 the Jordan cluster (C) with intrinsic invariant λ = l. -/
namespace TorsionCore

variable {K : Type*} [Field K]

/-- d₁ : C¹ → C², u ↦ (Xu, d₀u) = (0, w₁). -/
def d₁ : Matrix (Fin 3) (Fin 1) K := !![0; 1; 0]

/-- d₂ : C² → C³ for the (x, l)-cluster: α∧u ↦ −α∧w₁ + Lu, w₁ ↦ 0,
w₂ ↦ x·α∧w₁ + l·Lu (columns in the C²-basis, rows in the C³-basis). -/
def d₂ (x l : K) : Matrix (Fin 3) (Fin 3) K := !![-1, 0, x; 0, 0, 0; 1, 0, l]

/-- d₃ : C³ → C⁴: α∧w₁ ↦ 0, α∧w₂ ↦ −l·α∧Lu, Lu ↦ 0. -/
def d₃ (l : K) : Matrix (Fin 1) (Fin 3) K := !![0, -l, 0]

theorem d₂_mul_d₁ (x l : K) : d₂ x l * (d₁ : Matrix (Fin 3) (Fin 1) K) = 0 := by
  ext i j
  fin_cases j
  fin_cases i <;> simp [d₁, d₂, Matrix.mul_apply, Fin.sum_univ_succ]

theorem d₃_mul_d₂ (x l : K) : d₃ l * d₂ x l = 0 := by
  ext i j
  fin_cases i
  fin_cases j <;> simp [d₃, d₂, Matrix.mul_apply, Fin.sum_univ_succ]

/-- CD Def 3.2 basis-change matrix in degree 2: columns ∂a₁ = d₁u, then the complement
basis A² = (α∧u, w₂). -/
def D₂mat : Matrix (Fin 3) (Fin 3) K :=
  (Matrix.of ![d₁ *ᵥ ![1], ![1, 0, 0], ![0, 0, 1]])ᵀ

/-- Degree 3: columns ∂a₂ = (d₂(α∧u), d₂(w₂)), then the complement A³ = (−α∧w₂)
(the sign choice of zero_cluster_torsion_9_02 §2.3; it cancels in the torsion). -/
def D₃mat (x l : K) : Matrix (Fin 3) (Fin 3) K :=
  (Matrix.of ![d₂ x l *ᵥ ![1, 0, 0], d₂ x l *ᵥ ![0, 0, 1], ![0, -1, 0]])ᵀ

/-- Degree 4: the single column ∂a₃ = d₃(−α∧w₂); A⁴ = 0. -/
def D₄mat (l : K) : Matrix (Fin 1) (Fin 1) K :=
  (Matrix.of ![d₃ l *ᵥ ![0, -1, 0]])ᵀ

theorem det_D₂mat : (D₂mat : Matrix (Fin 3) (Fin 3) K).det = -1 := by
  rw [D₂mat, det_transpose, det_fin_three]
  simp [d₁]

theorem det_D₃mat (x l : K) : (D₃mat x l).det = -(l + x) := by
  rw [D₃mat, det_transpose, det_fin_three]
  simp [d₂]
  ring

theorem det_D₄mat (l : K) : (D₄mat l).det = l := by
  rw [D₄mat, det_transpose, det_fin_one]
  simp [d₃]

/-- CD Def 3.2 sign exponent N(C^•) = ½ Σ_j dim A^j (dim A^j + (−1)^{j+1}) for the
complement dimensions (1, 2, 1, 0) in degrees 1..4: ½(1·2 + 2·1 + 1·2 + 0) = 3. -/
def N_C : ℕ := 3

/-- CD Def 3.2 chirality-element sign exponent m(C^•) = ½ Σ_{j≤r} dim C^j (dim C^j +
(−1)^{r+j}), r = 2, dims (0, 1, 3): ½(0 + 1·0 + 3·4) = 6. -/
def m_C : ℕ := 6

theorem N_C_eq : (N_C : ℤ) = (1 * (1 + 1) + 2 * (2 - 1) + 1 * (1 + 1) + 0) / 2 := by
  decide

theorem m_C_eq : (m_C : ℤ) = (0 + 1 * (1 - 1) + 3 * (3 + 1)) / 2 := by
  decide

/-- The refined torsion τ(C^•, Γ_ϑ) of the (x, l)-cluster in CD's normalisation
(Def 3.2 with λ_j = D_j⁻¹, c_j = λ_j·μ(∂a_{j−1} ⊗ a_j)): τ = (−1)^{N+m} ∏ λ_j^{(−1)^j}
= (−1)^{N_C+m_C} · D₁ · D₂⁻¹ · D₃ · D₄⁻¹ with D₁ = det [u] = 1. The Γ_ϑ-basis signs in
c_Γ cancel pairwise (zero_cluster_torsion_9_02 §2.3, validated against CD Prop 6.2). -/
def refinedTorsion (x l : K) : K :=
  (-1) ^ (N_C + m_C) *
    ((!![(1 : K)]).det * (D₂mat : Matrix (Fin 3) (Fin 3) K).det⁻¹ * (D₃mat x l).det *
      (D₄mat l).det⁻¹)

theorem refinedTorsion_eq (x l : K) (hl : l ≠ 0) : refinedTorsion x l = -(l + x) / l := by
  rw [refinedTorsion, det_D₂mat, det_D₃mat, det_D₄mat, det_fin_one]
  simp only [N_C, m_C, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one]
  field_simp
  ring

/-- The nondegeneracy that makes the (x, l)-complex EXACT: D₃, D₄ ≠ 0 ⟺ l ∉ {0, −x}
(memo: λ ∉ {0, −1} for the Jordan cluster). -/
theorem dets_ne_zero (x l : K) (hl : l ≠ 0) (hlx : l + x ≠ 0) :
    (D₂mat : Matrix (Fin 3) (Fin 3) K).det ≠ 0 ∧ (D₃mat x l).det ≠ 0 ∧ (D₄mat l).det ≠ 0 := by
  rw [det_D₂mat, det_D₃mat, det_D₄mat]
  exact ⟨by norm_num, neg_ne_zero.mpr hlx, hl⟩

/-- Semisimple minimal cluster (D), a = 1: τ(C^•(0), Γ_ϑ) = −1 = (−1)^a. -/
theorem semisimple_cluster_torsion (l : K) (hl : l ≠ 0) : refinedTorsion 0 l = -1 := by
  rw [refinedTorsion_eq 0 l hl, add_zero, neg_div, div_self hl]

/-- Jordan J₂ cluster (C), Xw₂ = w₁ = d₀u, d₀w₂ = λ·Lu: τ(C^•(0), Γ_ϑ) = −(1+λ)/λ. -/
theorem jordan_cluster_torsion (l : K) (hl : l ≠ 0) : refinedTorsion 1 l = -(1 + l) / l := by
  rw [refinedTorsion_eq 1 l hl, add_comm]

/-- Lemma A shape (jordan_cluster_torsion_9_03 §3.3a): with the Jordan invariant
λ = s_p/(s_z − s_p) of the arriving pole s_p and zero s_z, τ = −s_z/s_p. -/
theorem jordan_torsion_eq_neg_ratio (sp sz : K) (hsp : sp ≠ 0) (hne : sz ≠ sp) :
    refinedTorsion 1 (sp / (sz - sp)) = -(sz / sp) := by
  have h : sz - sp ≠ 0 := sub_ne_zero.mpr hne
  rw [jordan_cluster_torsion _ (div_ne_zero hsp h)]
  field_simp
  ring

end TorsionCore

/-! ## §2 (P2) The order count m = c₂ − 2c₁ -/
namespace OrderCount

variable {K : Type*} [Field K] {V₁ V₂ V₃ : Type*}
  [AddCommGroup V₁] [Module K V₁] [FiniteDimensional K V₁]
  [AddCommGroup V₂] [Module K V₂] [FiniteDimensional K V₂]
  [AddCommGroup V₃] [Module K V₃]

/-- Rank–nullity twice: for an exact 0 → V₁ → V₂ → V₃ → 0,
dim V₂ = dim V₁ + dim V₃. -/
theorem finrank_middle_of_exact (f : V₁ →ₗ[K] V₂) (g : V₂ →ₗ[K] V₃)
    (hf : Function.Injective f) (hfg : LinearMap.range f = LinearMap.ker g)
    (hg : Function.Surjective g) :
    Module.finrank K V₂ = Module.finrank K V₁ + Module.finrank K V₃ := by
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  have h2 := LinearMap.finrank_range_add_finrank_ker g
  rw [LinearMap.ker_eq_bot.mpr hf, finrank_bot, add_zero] at h1
  rw [LinearMap.range_eq_top.mpr hg, finrank_top, ← hfg, h1] at h2
  omega

/-- CD (5.9) footnote 5 with q = 2: the order of ζ at a resonance is
Σ_k (−1)^k dim C₀^k (degrees 0,2,4 zeros, degrees 1,3 poles). -/
def zetaOrder (c : Fin 5 → ℕ) : ℤ := ∑ k : Fin 5, (-1 : ℤ) ^ (k : ℕ) * (c k : ℤ)

/-- With c₀ = c₄ = 0 (DGRS Lemma 7.4 + ⋆) and c₃ = c₁ (⋆): m = c₂ − 2c₁. -/
theorem zetaOrder_eq (c : Fin 5 → ℕ) (h0 : c 0 = 0) (h4 : c 4 = 0) (h31 : c 3 = c 1) :
    zetaOrder c = (c 2 : ℤ) - 2 * c 1 := by
  simp only [zetaOrder, Fin.sum_univ_five, h0, h4, h31]
  norm_num
  ring

/-- The (1,1,1) chain headed by the non-closed 1-form: a simple POLE. -/
theorem zetaOrder_pole_chain : zetaOrder ![0, 1, 1, 1, 0] = -1 := by decide

/-- A pure degree-2 state: a simple ZERO. -/
theorem zetaOrder_pure_zero : zetaOrder ![0, 0, 1, 0, 0] = 1 := by decide

/-- The generic crossing cluster (0,1,2,1,0): order 0, ζ regular at 0. -/
theorem zetaOrder_crossing_cluster : zetaOrder ![0, 1, 2, 1, 0] = 0 := by decide

/-- P2: exact reduced complex + duality ⇒ c₂ = 2c₁ ⇒ the ζ-order at 0 is 0. -/
theorem order_zero_of_exact (f : V₁ →ₗ[K] V₂) (g : V₂ →ₗ[K] V₃)
    (hf : Function.Injective f) (hfg : LinearMap.range f = LinearMap.ker g)
    (hg : Function.Surjective g) (c : Fin 5 → ℕ) (hacyc : c 0 = 0 ∧ c 4 = 0)
    (hdual : c 3 = c 1)
    (hdims : c 1 = Module.finrank K V₁ ∧ c 2 = Module.finrank K V₂ ∧
      c 3 = Module.finrank K V₃) :
    zetaOrder c = 0 := by
  have hmid := finrank_middle_of_exact f g hf hfg hg
  rw [zetaOrder_eq c hacyc.1 hacyc.2 hdual, hdims.2.1, hdims.1]
  have h31 : Module.finrank K V₃ = Module.finrank K V₁ := by
    rw [← hdims.2.2, ← hdims.1, hdual]
  rw [hmid, h31]
  push_cast
  ring

end OrderCount

/-! ## §3 (P3) Crossing existence (IVT + monotonicity; the IFT step of memo A5) -/
namespace Crossing

/-- A C¹ real branch with s(0) < 0 and ∂_τ s ≥ r₀ > 0 crosses 0 exactly once, at some
σ ∈ (0, |s(0)|/r₀]. -/
theorem crossing_exists_unique {s ds : ℝ → ℝ} {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hderiv : ∀ τ, HasDerivAt s (ds τ) τ) (hlow : ∀ τ, r₀ ≤ ds τ) (hs0 : s 0 < 0) :
    ∃ σ, 0 < σ ∧ σ ≤ |s 0| / r₀ ∧ s σ = 0 ∧ ∀ τ, s τ = 0 → τ = σ := by
  have hdiff : Differentiable ℝ s := fun τ => (hderiv τ).differentiableAt
  have hderiv' : ∀ τ, deriv s τ = ds τ := fun τ => (hderiv τ).deriv
  have hmono : StrictMono s := strictMono_of_deriv_pos fun τ => by
    rw [hderiv']; exact lt_of_lt_of_le hr₀ (hlow τ)
  set T := -s 0 / r₀ with hT
  have hTpos : 0 < T := div_pos (neg_pos.mpr hs0) hr₀
  have hgrow : r₀ * (T - 0) ≤ s T - s 0 :=
    mul_sub_le_image_sub_of_le_deriv hdiff (fun τ => by rw [hderiv']; exact hlow τ) hTpos.le
  have hrT : r₀ * T = -s 0 := by
    rw [hT, mul_div_cancel₀ _ hr₀.ne']
  have hsT : 0 ≤ s T := by linarith
  obtain ⟨σ, hσmem, hσ⟩ : (0 : ℝ) ∈ s '' Set.Icc 0 T :=
    intermediate_value_Icc hTpos.le hdiff.continuous.continuousOn ⟨hs0.le, hsT⟩
  refine ⟨σ, ?_, ?_, hσ, ?_⟩
  · exact hmono.lt_iff_lt.mp (by rw [hσ]; exact hs0)
  · rw [abs_of_neg hs0]; exact hσmem.2
  · intro τ hτ; exact hmono.injective (hτ.trans hσ.symm)

end Crossing

/-! ## §4 (P4) Rate-ratio bookkeeping (memo crossing_rate_ratio_9_03 §1, §3) -/
namespace RateRatio

/-- `f(τ) = c·(τ − σ)·(1 + o(1))` as τ → σ, τ ≠ σ: the slope quotient tends to `c`. -/
def LinearArrival (f : ℝ → ℝ) (c σ : ℝ) : Prop :=
  Tendsto (fun τ => f τ / (τ - σ)) (𝓝[≠] σ) (𝓝 c)

theorem eventually_ne_nhdsNE (σ : ℝ) : ∀ᶠ τ in 𝓝[≠] σ, τ ≠ σ :=
  eventually_nhdsWithin_of_forall fun _ h => h

/-- The memos' `(1 + o(1))` form implies linear arrival. -/
theorem linearArrival_of_one_add_o {f e : ℝ → ℝ} {c σ : ℝ}
    (hf : ∀ τ, f τ = c * (τ - σ) * (1 + e τ)) (he : Tendsto e (𝓝[≠] σ) (𝓝 0)) :
    LinearArrival f c σ := by
  have h : Tendsto (fun τ => c * (1 + e τ)) (𝓝[≠] σ) (𝓝 (c * (1 + 0))) :=
    (tendsto_const_nhds.add he).const_mul c
  rw [add_zero, mul_one] at h
  refine h.congr' ((eventually_ne_nhdsNE σ).mono fun τ hτ => ?_)
  have hne : τ - σ ≠ 0 := sub_ne_zero.mpr hτ
  change c * (1 + e τ) = f τ / (τ - σ)
  rw [hf τ]
  field_simp

/-- A branch differentiable at σ and vanishing there arrives linearly with its slope. -/
theorem linearArrival_of_hasDerivAt {f : ℝ → ℝ} {c σ : ℝ} (hf : HasDerivAt f c σ)
    (h0 : f σ = 0) : LinearArrival f c σ := by
  have h := hasDerivAt_iff_tendsto_slope.mp hf
  refine h.congr' (Eventually.of_forall fun τ => ?_)
  rw [slope_def_field, h0, sub_zero]

/-- z ~ a(τ−σ), p ~ b(τ−σ), b ≠ 0 ⇒ z/p → a/b. -/
theorem ratio_tendsto {z p : ℝ → ℝ} {a b σ : ℝ} (hz : LinearArrival z a σ)
    (hp : LinearArrival p b σ) (hb : b ≠ 0) :
    Tendsto (fun τ => z τ / p τ) (𝓝[≠] σ) (𝓝 (a / b)) := by
  refine (hz.div hp hb).congr' ((eventually_ne_nhdsNE σ).mono fun τ hτ => ?_)
  simp only [Pi.div_apply]
  rw [div_div_div_cancel_right₀ (sub_ne_zero.mpr hτ)]

theorem eventually_ne_zero_of_linearArrival {f : ℝ → ℝ} {c σ : ℝ}
    (hf : LinearArrival f c σ) (hc : c ≠ 0) : ∀ᶠ τ in 𝓝[≠] σ, f τ ≠ 0 :=
  (hf.eventually_ne hc).mono fun τ hτ h0 => hτ (by rw [h0, zero_div])

/-- THE VALUE AT THE CROSSING. If ζ(0; g_τ) = R(τ)·z(τ)/p(τ) equals τ_R for every
τ ≠ σ and the regular factor R is continuous at σ, then R(σ) = τ_R·(b/a): the
meromorphic value at the crossing is τ_R times the limiting pole/zero rate ratio. -/
theorem crossing_value {z p R : ℝ → ℝ} {a b σ τR : ℝ}
    (hz : LinearArrival z a σ) (hp : LinearArrival p b σ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hoff : ∀ τ, τ ≠ σ → R τ * z τ / p τ = τR) (hR : ContinuousAt R σ) :
    R σ = τR * (b / a) := by
  have hpz := ratio_tendsto hp hz ha
  have hlim : Tendsto R (𝓝[≠] σ) (𝓝 (τR * (b / a))) := by
    refine (hpz.const_mul τR).congr' ?_
    filter_upwards [eventually_ne_nhdsNE σ, eventually_ne_zero_of_linearArrival hz ha,
      eventually_ne_zero_of_linearArrival hp hb] with τ hτ hzτ hpτ
    have h := hoff τ hτ
    rw [← h]
    field_simp
  exact tendsto_nhds_unique (hR.tendsto.mono_left nhdsWithin_le_nhds) hlim

/-- The crossing value differs from τ_R exactly when the rates are unbalanced. -/
theorem crossing_value_ne_iff {τR a b : ℝ} (hτR : τR ≠ 0) (ha : a ≠ 0) :
    τR * (b / a) ≠ τR ↔ b ≠ a := by
  rw [Ne, Ne, not_iff_not]
  constructor
  · intro h
    have h' : b / a = 1 := mul_left_cancel₀ hτR (h.trans (mul_one τR).symm)
    exact (div_eq_one_iff_eq ha).mp h'
  · rintro rfl
    rw [div_self ha, mul_one]

end RateRatio

/-! ## §5 (P5) THE CAPSTONE — the input ledger

Every hypothesis is ONE analytic fact a human verifies against the cited source; the
conclusion is the memo's verdict. Objects: `S θ τ` = the non-closed degree-1 resonance
branch s_nc(θ,τ) (complex-valued a priori), `ds θ τ` its τ-derivative, `z` = the pure
degree-2 zero branch forced through 0 at the crossing, `R` = the regular factor F(0,·)
of CD (6.5) (so ζ(0; g_τ) = R(τ)·z(τ)/s_nc(τ) off the crossing and ζ(0; g_σ) = R(σ)),
`c` = the C₀-dimensions of the zero cluster at the crossing, `V₁ V₂ V₃` = C₀¹, C₀², C₀³
at the crossing, `τR` = τ_R(χ_θ). -/
namespace Capstone

open TorsionCore OrderCount Crossing RateRatio

/-- FRIED FAILS AT THE CROSSING METRIC, from the input ledger.

Hypotheses (source verbatim in the memos):
* `hτR` — τ_R(χ_θ) ≠ 0 (Reidemeister torsion of an acyclic representation).
* `hdouble` — at g_hyp the non-closed branch sits at the doubled real degree-1 resonance
  s*(θ) = −1 + √(1−μ₀(θ)) < 0: DGRS Prop 7.6 (7.6)/(7.7), factor Z_{S,σ₀}(λ+2)² ⇒
  multiplicity 2, + DFG Thm 2 (location/reality) — memo A1–A2.
* `hsym` — s ↦ s̄ symmetry (adjoint ∘ time reversal J) keeps the simple branch REAL
  along the real family — memo A3.
* `hrate_nonclosed` — CDDP (4.22)/(4.38) first variation of the non-closed state,
  r₀ ≠ 0 for b in CDDP's open dense set (Thm 1(2)); sign normalised so the branch
  moves toward 0, bound taken uniform on the τ-range used — memo A4–A5.
* `hrate_zero` — at a crossing the pure degree-2 zero arrives linearly with slope
  a ≠ 0 UNEQUAL to the pole's slope: CDDP Cor 4.1 (m_{2,0}(0) = b₁ + 2 at θ = 0, the
  pole leaves 0 alone) + the ±s* mirror at g_hyp ⇒ e₁(θ,σ) = O(θ⁴) while |s*| = Θ(θ²),
  so a/b = |s*|/e₁ ≠ 1 — crossing_rate_ratio_9_03 §2.2–§3.
* `hcont` — the regular factor F(0,·) of CD (6.5) is continuous at the crossing
  (continuity of resonances / analytic Riesz projector, CD Thm 4/5 setting).
* `hfried_off` — off the crossing 0 ∉ Res and ζ(0; g_τ) = R(τ)·z(τ)/s_nc(τ) = τ_R:
  DGRS Thm 2 local constancy + Fried/Shen at g_hyp — memo A6, rate-ratio §1.
* `hexact` — the reduced resonant complex (C₀•(0), d₀) at the crossing is exact:
  Dang–Rivière exactness of (C•, d∇) (DGRS (7.1)) in the generic c₂ = 2 case
  (rate-ratio §2.4; the degenerate 3-chain c₂ = 3 gives m = +1 and fails Fried too).
* `hacyc` — c₀ = c₄ = 0: DGRS Lemma 7.4 (+ ⋆) for acyclic unitary ρ.
* `hdual` — c₃ = c₁: ⋆-duality, DGRS Lemma 7.2.
* `hdims` — bookkeeping: c_k = dim C₀^k for k = 1, 2, 3.

Conclusion: a unique crossing σ ∈ (0, |s*|/r₀]; ζ is regular at 0 there (order 0);
the pole/zero rate ratio exists, ≠ 1; ζ(0; g_σ) = R(σ) = τ_R · ratio ≠ τ_R; and the
refined torsion of the limiting J₂ cluster is −(zero rate)/(pole rate) (Lemma A). -/
theorem fried_fails_at_crossing_of_inputs
    {K : Type*} [Field K] {V₁ V₂ V₃ : Type*}
    [AddCommGroup V₁] [Module K V₁] [FiniteDimensional K V₁]
    [AddCommGroup V₂] [Module K V₂] [FiniteDimensional K V₂]
    [AddCommGroup V₃] [Module K V₃]
    (S : ℝ → ℝ → ℂ) (ds : ℝ → ℝ → ℝ) (z R : ℝ → ℝ) (c : Fin 5 → ℕ)
    (θ sStar r₀ τR : ℝ)
    (hτR : τR ≠ 0)
    (hdouble : S θ 0 = (sStar : ℂ) ∧ sStar < 0)
    (hsym : ∀ τ, (S θ τ).im = 0)
    (hrate_nonclosed : 0 < r₀ ∧
      ∀ τ, HasDerivAt (fun τ => (S θ τ).re) (ds θ τ) τ ∧ r₀ ≤ ds θ τ)
    (hrate_zero : ∀ τ₀, S θ τ₀ = 0 → ∃ (a : ℝ) (e : ℝ → ℝ), a ≠ 0 ∧ a ≠ ds θ τ₀ ∧
      (∀ τ, z τ = a * (τ - τ₀) * (1 + e τ)) ∧ Tendsto e (𝓝[≠] τ₀) (𝓝 0))
    (hcont : ∀ τ₀, S θ τ₀ = 0 → ContinuousAt R τ₀)
    (hfried_off : ∀ τ, S θ τ ≠ 0 → R τ * z τ / (S θ τ).re = τR)
    (hexact : ∃ (f : V₁ →ₗ[K] V₂) (g : V₂ →ₗ[K] V₃), Function.Injective f ∧
      LinearMap.range f = LinearMap.ker g ∧ Function.Surjective g)
    (hacyc : c 0 = 0 ∧ c 4 = 0) (hdual : c 3 = c 1)
    (hdims : c 1 = Module.finrank K V₁ ∧ c 2 = Module.finrank K V₂ ∧
      c 3 = Module.finrank K V₃) :
    ∃ σ, 0 < σ ∧ σ ≤ |sStar| / r₀ ∧ S θ σ = 0 ∧ (∀ τ, S θ τ = 0 → τ = σ) ∧
      zetaOrder c = 0 ∧
      ∃ a ratio : ℝ, a ≠ 0 ∧ ds θ σ ≠ 0 ∧
        Tendsto (fun τ => (S θ τ).re / z τ) (𝓝[≠] σ) (𝓝 ratio) ∧
        ratio = ds θ σ / a ∧ ratio ≠ 1 ∧ R σ = τR * ratio ∧ R σ ≠ τR ∧
        refinedTorsion 1 (ds θ σ / (a - ds θ σ)) = -(a / ds θ σ) := by
  obtain ⟨hr₀, hrate⟩ := hrate_nonclosed
  -- the real branch s_nc(θ, ·)
  have hs0' : (S θ 0).re = sStar := by rw [hdouble.1, Complex.ofReal_re]
  have hs0 : (S θ 0).re < 0 := by rw [hs0']; exact hdouble.2
  -- P3: the crossing
  obtain ⟨σ, hσpos, hσle, hσ0, huniq⟩ :=
    crossing_exists_unique hr₀ (fun τ => (hrate τ).1) (fun τ => (hrate τ).2) hs0
  have hSσ : S θ σ = 0 := Complex.ext (by simpa using hσ0) (by simpa using hsym σ)
  have hcross : ∀ τ, S θ τ = 0 → τ = σ := fun τ h => huniq τ (by rw [h, Complex.zero_re])
  have hoff : ∀ τ, τ ≠ σ → S θ τ ≠ 0 := fun τ hτ h => hτ (hcross τ h)
  -- P4: rates and value
  obtain ⟨a, e, ha, hab, hz, he⟩ := hrate_zero σ hSσ
  have hzA : LinearArrival z a σ := linearArrival_of_one_add_o hz he
  have hpA : LinearArrival (fun τ => (S θ τ).re) (ds θ σ) σ :=
    linearArrival_of_hasDerivAt (hrate σ).1 hσ0
  have hb : ds θ σ ≠ 0 := (lt_of_lt_of_le hr₀ (hrate σ).2).ne'
  have hval : R σ = τR * (ds θ σ / a) :=
    crossing_value hzA hpA ha hb (fun τ hτ => hfried_off τ (hoff τ hτ)) (hcont σ hSσ)
  have hratio : ds θ σ / a ≠ 1 := fun h1 => hab ((div_eq_one_iff_eq ha).mp h1).symm
  -- P2: the order
  obtain ⟨f, g, hf, hfg, hg⟩ := hexact
  have hord : zetaOrder c = 0 := order_zero_of_exact f g hf hfg hg c hacyc hdual hdims
  refine ⟨σ, hσpos, by rwa [hs0'] at hσle, hSσ, hcross, hord, a, ds θ σ / a, ha, hb,
    ratio_tendsto hpA hzA ha, rfl, hratio, hval, ?_, ?_⟩
  · rw [hval]; exact (crossing_value_ne_iff hτR ha).mpr fun h => hratio (by rw [h, div_self ha])
  · -- P1: the Lemma A reading of the limiting J₂ cluster
    exact jordan_torsion_eq_neg_ratio (ds θ σ) a hb hab

end Capstone

end FriedCrossing
