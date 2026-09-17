/-
FRIED AT A CODIMENSION-ONE CROSSING — THE LEDGER (9/03; vault memos
fried_counterexample_rederivation_9_03 [cleanest statement], crossing_rate_ratio_9_03
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
  [9/16: this capstone, `Crossing.crossing_exists_unique` and `RateRatio.crossing_value` were REMOVED for the
  Palomar entry as superseded; the compared theorem is `fried_counterexample_of_resolvent_inputs`
  (fried_counterexample_main), which uses the `_local` forms below.]
                    analytic inputs (hdouble, hsym, hrate_nonclosed, hrate_zero, hcont,
                    hfried_off, hexact, hacyc, hdual; bookkeeping hdims, hτR).
-/
import B1s.fried_statement_defs_9_14

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

theorem d₂_mul_d₁ (x l : K) : d₂ x l * (d₁ : Matrix (Fin 3) (Fin 1) K) = 0 := by
  ext i j
  fin_cases j
  fin_cases i <;> simp [d₁, d₂, Matrix.mul_apply, Fin.sum_univ_succ]

theorem d₃_mul_d₂ (x l : K) : d₃ l * d₂ x l = 0 := by
  ext i j
  fin_cases i
  fin_cases j <;> simp [d₃, d₂, Matrix.mul_apply, Fin.sum_univ_succ]

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

theorem N_C_eq : (N_C : ℤ) = (1 * (1 + 1) + 2 * (2 - 1) + 1 * (1 + 1) + 0) / 2 := by
  decide

theorem m_C_eq : (m_C : ℤ) = (0 + 1 * (1 - 1) + 3 * (3 + 1)) / 2 := by
  decide

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

end Capstone

end FriedCrossing
