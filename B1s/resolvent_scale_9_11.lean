/-
THE RESOLVENT ON A BANACH SCALE IS C^k WITH LOSS — the operator-calculus shell of input (B) (9/11).

Context (vault: input_b_cauchy_route_9_09 §1, chronology 9/11). Input (B) says the cluster matrices
are jointly C³ in (θ,τ). The derivation in the literature is: CDDP Lemma 4.3 gives the resolvent
R(x,λ) of the twisted, deformed generator P(x) − λ bounded LOCALLY UNIFORMLY on each level H^{r,s}
of the anisotropic scale; the resolvent identity (4.12)
    R(x) − R(y) = R(x)(P(y) − P(x))R(y)          (as maps H_s → H_{s−1})
then gives continuity with loss, (4.13) the first derivative with loss, and iterating gives every
derivative, each costing levels. This file proves that iteration ABSTRACTLY: no dynamics, no
anisotropic spaces — a scale of real Banach spaces with coherent inclusions, a resolvent family
bounded locally uniformly on every level, a generator family smooth in the parameter, and the
inverse relations. Everything downstream (the contour projector, the frame, the cluster matrices) is
in the companion `cluster_from_resolvent_9_11.lean`.

Conventions. All spaces are REAL Banach spaces and all operators ℝ-linear: the complex structure
of the anisotropic spaces is an extra operator J (companion file); here λ ∈ ℂ is just two real
parameters inside the parameter space X. Levels are indexed by ℕ, n = 0 the ROUGHEST space (largest),
and `incl a b : H a →L H b` for b ≤ a is the inclusion (coherent: `incl_refl`, `incl_trans`). A family
"with loss" is x ↦ incl a b ∘ R a x : H a → H b, b < a.

Loss bookkeeping (crude, sufficient): continuity costs 1 level, differentiability 2, and C^k costs
L k := 2^(k+1) − 1 (L 0 = 1, L (k+1) = 2·L k + 1), because the derivative is a product of two
resolvent families with loss and one smooth factor. CDDP supply every level (r > C₀ + |s| + k), so a
longer scale is free.

⚡AUDIT CRITERION: ZERO axioms of its own — `#print axioms` on every theorem = built-ins only.
-/
import B1s.fried_statement_defs_9_14

set_option linter.style.header false

namespace FriedCrossing

open Filter Topology ContinuousLinearMap Asymptotics

/-! ## §1 Banach scales and resolvent families -/
namespace Scale

universe u

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

variable {S : BanachScale.{u}} (F : ResolventFamily S X)

/-- THE RESOLVENT IDENTITY (CDDP (4.12)), derived from the inverse relations:
incl (R x − R y) = R x (B y − B x) R y as maps H (n+1) → H n. -/
theorem resolvent_identity (n : ℕ) (x y : X) :
    (S.incl (n + 1) n (Nat.le_succ n)).comp (F.R (n + 1) x - F.R (n + 1) y) =
      ((F.R n x).comp (F.B n y - F.B n x)).comp (F.R (n + 1) y) := by
  have h1 : ((F.R n x).comp (F.B n y - F.B n x)).comp (F.R (n + 1) y) =
      (F.R n x).comp ((F.B n y).comp (F.R (n + 1) y)) -
        ((F.R n x).comp (F.B n x)).comp (F.R (n + 1) y) := by
    rw [comp_sub, sub_comp, comp_assoc]
  rw [h1, F.inv_right, F.inv_left, ← F.R_incl, comp_sub]

/-! ## §2 Compatibilities across several levels; continuity with loss -/

/-- The resolvent commutes with every inclusion. -/
theorem R_incl_gen (a b : ℕ) (hab : b ≤ a) (x : X) :
    (S.incl a b hab).comp (F.R a x) = (F.R b x).comp (S.incl a b hab) := by
  induction a with
  | zero =>
    have hb : b = 0 := Nat.le_zero.mp hab
    subst hb
    rw [S.incl_refl]; simp
  | succ a ih =>
    rcases Nat.eq_or_lt_of_le hab with h | h
    · subst h; rw [S.incl_refl]; simp
    · have hba : b ≤ a := Nat.lt_succ_iff.mp h
      rw [← S.incl_trans (a + 1) a b (Nat.le_succ a) hba, comp_assoc, F.R_incl, ← comp_assoc,
        ih hba, comp_assoc]

/-- The generator commutes with every inclusion. -/
theorem B_incl_gen (a b : ℕ) (hab : b ≤ a) (x : X) :
    (S.incl a b hab).comp (F.B a x) = (F.B b x).comp (S.incl (a + 1) (b + 1) (by omega)) := by
  induction a with
  | zero =>
    have hb : b = 0 := Nat.le_zero.mp hab
    subst hb
    rw [S.incl_refl, S.incl_refl]; simp
  | succ a ih =>
    rcases Nat.eq_or_lt_of_le hab with h | h
    · subst h; rw [S.incl_refl, S.incl_refl]; simp
    · have hba : b ≤ a := Nat.lt_succ_iff.mp h
      rw [← S.incl_trans (a + 1) a b (Nat.le_succ a) hba, comp_assoc, F.B_incl, ← comp_assoc,
        ih hba, comp_assoc, S.incl_trans]

/-- Loss-one continuity (CDDP: "locally Lipschitz continuous in τ"):
x ↦ incl (n+1) n ∘ R (n+1) x. -/
theorem locallyLipschitz_loss_one (n : ℕ) :
    LocallyLipschitz fun x => (S.incl (n + 1) n (Nat.le_succ n)).comp (F.R (n + 1) x) := by
  intro x₀
  obtain ⟨C, hC⟩ := F.bdd n x₀
  obtain ⟨C', hC'⟩ := F.bdd (n + 1) x₀
  obtain ⟨K, t, ht, hK⟩ := (F.smooth n).of_le le_top |>.locallyLipschitz x₀
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) hC.self_of_nhds
  have hC'0 : 0 ≤ C' := le_trans (norm_nonneg _) hC'.self_of_nhds
  refine ⟨⟨C * K * C', by positivity⟩, {x | ‖F.R n x‖ ≤ C} ∩ {x | ‖F.R (n + 1) x‖ ≤ C'} ∩ t,
    inter_mem (inter_mem hC hC') ht, ?_⟩
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  obtain ⟨⟨hxC, hxC'⟩, hxt⟩ := hx
  obtain ⟨⟨hyC, hyC'⟩, hyt⟩ := hy
  rw [dist_eq_norm, ← comp_sub, resolvent_identity]
  calc ‖((F.R n x).comp (F.B n y - F.B n x)).comp (F.R (n + 1) y)‖
      ≤ ‖(F.R n x).comp (F.B n y - F.B n x)‖ * ‖F.R (n + 1) y‖ := opNorm_comp_le _ _
    _ ≤ ‖F.R n x‖ * ‖F.B n y - F.B n x‖ * ‖F.R (n + 1) y‖ := by
        gcongr; exact opNorm_comp_le _ _
    _ ≤ C * (K * dist x y) * C' := by
        have h1 : ‖F.R n x‖ ≤ C := hxC
        have h2 : ‖F.B n y - F.B n x‖ ≤ K * dist x y := by
          rw [← dist_eq_norm, dist_comm]; exact hK.dist_le_mul x hxt y hyt
        have h3 : ‖F.R (n + 1) y‖ ≤ C' := hyC'
        exact mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) hC0) h3 (norm_nonneg _)
          (mul_nonneg hC0 (by positivity))
    _ = ((⟨C * K * C', by positivity⟩ : NNReal) : ℝ) * dist x y := by push_cast; ring

/-- Continuity with any loss ≥ 1, in the shape used downstream. -/
theorem continuous_loss (a b : ℕ) (hab : b + 1 ≤ a) :
    Continuous fun x => (S.incl a b (by omega)).comp (F.R a x) := by
  have heq : (fun x => (S.incl a b (by omega)).comp (F.R a x)) =
      fun x => ((S.incl (b + 1) b (Nat.le_succ b)).comp (F.R (b + 1) x)).comp
        (S.incl a (b + 1) hab) := by
    funext x
    rw [comp_assoc, ← R_incl_gen F a (b + 1) hab, ← comp_assoc, S.incl_trans]
  rw [heq]
  exact (locallyLipschitz_loss_one F b).continuous.clm_comp continuous_const

/-! ## §3 The derivative with loss two (CDDP (4.13)) -/

/-- The derivative of x ↦ incl a b ∘ R a x at x, for a ≥ b + 2, as a continuous linear map in the
direction h: −(incl (b+1) b ∘ R (b+1) x) ∘ (∂B (b+1) x h) ∘ (incl a (b+2) ∘ R a x). -/
noncomputable def derivLoss (a b : ℕ) (hab : b + 2 ≤ a) (x : X) :
    X →L[ℝ] (S.H a →L[ℝ] S.H b) :=
  -(((compL ℝ (S.H a) (S.H (b + 1)) (S.H b))
      ((S.incl (b + 1) b (Nat.le_succ b)).comp (F.R (b + 1) x))).comp
    (((compL ℝ (S.H a) (S.H (b + 2)) (S.H (b + 1))).flip
      ((S.incl a (b + 2) hab).comp (F.R a x))).comp (fderiv ℝ (F.B (b + 1)) x)))

theorem derivLoss_apply (a b : ℕ) (hab : b + 2 ≤ a) (x : X) (h : X) :
    derivLoss F a b hab x h =
      -(((S.incl (b + 1) b (Nat.le_succ b)).comp (F.R (b + 1) x)).comp
        ((fderiv ℝ (F.B (b + 1)) x h).comp ((S.incl a (b + 2) hab).comp (F.R a x)))) := by
  simp [derivLoss, compL_apply, flip_apply]

/-- incl a b ∘ (R a x − R a x₀) = (incl (b+1) b ∘ R (b+1) x) ∘ (B (b+1) x₀ − B (b+1) x) ∘
(incl a (b+2) ∘ R a x₀): the identity at level b+1, pushed through the inclusions. -/
theorem diff_eq (a b : ℕ) (hab : b + 2 ≤ a) (x x₀ : X) :
    (S.incl a b (by omega)).comp (F.R a x - F.R a x₀) =
      (((S.incl (b + 1) b (Nat.le_succ b)).comp (F.R (b + 1) x)).comp
        (F.B (b + 1) x₀ - F.B (b + 1) x)).comp ((S.incl a (b + 2) hab).comp (F.R a x₀)) := by
  have h1 : (S.incl a b (by omega)).comp (F.R a x - F.R a x₀) =
      (S.incl (b + 1) b (Nat.le_succ b)).comp
        (((S.incl (b + 2) (b + 1) (Nat.le_succ _)).comp (F.R (b + 2) x - F.R (b + 2) x₀)).comp
          (S.incl a (b + 2) hab)) := by
    rw [comp_assoc, sub_comp, ← R_incl_gen F a (b + 2) hab x, ← R_incl_gen F a (b + 2) hab x₀,
      ← comp_sub, ← comp_assoc, ← comp_assoc, S.incl_trans, S.incl_trans]
  rw [h1, resolvent_identity]
  simp only [comp_assoc]
  rw [R_incl_gen F a (b + 2) hab x₀]

/-- THE DERIVATIVE WITH LOSS. For a ≥ b + 2 the family x ↦ incl a b ∘ R a x is Fréchet
differentiable with derivative `derivLoss`. Proof: the identity gives the difference as a product;
subtracting the candidate derivative leaves (loss-one Lipschitz) × O(h) = O(h²) plus (bounded) × o(h). -/
theorem hasFDerivAt_loss (a b : ℕ) (hab : b + 2 ≤ a) (x₀ : X) :
    HasFDerivAt (fun x => (S.incl a b (by omega)).comp (F.R a x)) (derivLoss F a b hab x₀) x₀ := by
  set U : X → (S.H (b + 1) →L[ℝ] S.H b) :=
    fun x => (S.incl (b + 1) b (Nat.le_succ b)).comp (F.R (b + 1) x) with hU
  set V : S.H a →L[ℝ] S.H (b + 2) := (S.incl a (b + 2) hab).comp (F.R a x₀) with hV
  -- Lipschitz data for U near x₀, Lipschitz data for B (b+1) near x₀
  obtain ⟨K, t, ht, hK⟩ := locallyLipschitz_loss_one F b x₀
  obtain ⟨K', t', ht', hK'⟩ := (F.smooth (b + 1)).of_le le_top |>.locallyLipschitz x₀
  have hBd : HasFDerivAt (F.B (b + 1)) (fderiv ℝ (F.B (b + 1)) x₀) x₀ :=
    ((F.smooth (b + 1)).differentiable (by simp) x₀).hasFDerivAt
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  -- the error splits as e₁ + e₂
  have hsplit : ∀ h : X,
      (S.incl a b (by omega)).comp (F.R a (x₀ + h)) - (S.incl a b (by omega)).comp (F.R a x₀) -
        derivLoss F a b hab x₀ h =
      ((U (x₀ + h) - U x₀).comp (F.B (b + 1) x₀ - F.B (b + 1) (x₀ + h))).comp V -
        ((U x₀).comp
          (F.B (b + 1) (x₀ + h) - F.B (b + 1) x₀ - fderiv ℝ (F.B (b + 1)) x₀ h)).comp V := by
    intro h
    rw [← comp_sub, diff_eq F a b hab (x₀ + h) x₀, derivLoss_apply]
    simp only [hU, hV, sub_comp, comp_sub, comp_assoc, sub_neg_eq_add]
    abel
  have he₁ : (fun h : X =>
      ((U (x₀ + h) - U x₀).comp (F.B (b + 1) x₀ - F.B (b + 1) (x₀ + h))).comp V)
      =o[𝓝 0] fun h => h := by
    have hbig : (fun h : X => ((U (x₀ + h) - U x₀).comp
        (F.B (b + 1) x₀ - F.B (b + 1) (x₀ + h))).comp V) =O[𝓝 0] fun h => ‖h‖ ^ 2 := by
      have hmem : ∀ᶠ h : X in 𝓝 0, x₀ + h ∈ t ∩ t' := by
        have : Tendsto (fun h : X => x₀ + h) (𝓝 0) (𝓝 x₀) := by
          simpa using (tendsto_id (x := 𝓝 (0 : X))).const_add x₀
        exact this (inter_mem ht ht')
      refine IsBigO.of_bound (K * K' * ‖V‖) ?_
      filter_upwards [hmem] with h hh
      have hUl : ‖U (x₀ + h) - U x₀‖ ≤ K * ‖h‖ := by
        have := hK.dist_le_mul (x₀ + h) hh.1 x₀ (mem_of_mem_nhds ht)
        rwa [dist_eq_norm, dist_eq_norm, add_sub_cancel_left] at this
      have hBl : ‖F.B (b + 1) x₀ - F.B (b + 1) (x₀ + h)‖ ≤ K' * ‖h‖ := by
        have := hK'.dist_le_mul x₀ (mem_of_mem_nhds ht') (x₀ + h) hh.2
        rwa [dist_eq_norm, dist_eq_norm, sub_add_cancel_left, norm_neg] at this
      calc ‖((U (x₀ + h) - U x₀).comp (F.B (b + 1) x₀ - F.B (b + 1) (x₀ + h))).comp V‖
          ≤ ‖U (x₀ + h) - U x₀‖ * ‖F.B (b + 1) x₀ - F.B (b + 1) (x₀ + h)‖ * ‖V‖ := by
            refine le_trans (opNorm_comp_le _ _) ?_
            gcongr; exact opNorm_comp_le _ _
        _ ≤ (K * ‖h‖) * (K' * ‖h‖) * ‖V‖ := by gcongr
        _ = K * K' * ‖V‖ * ‖‖h‖ ^ 2‖ := by
            rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; ring
    exact hbig.trans_isLittleO (isLittleO_norm_pow_id one_lt_two)
  have he₂ : (fun h : X => ((U x₀).comp
      (F.B (b + 1) (x₀ + h) - F.B (b + 1) x₀ - fderiv ℝ (F.B (b + 1)) x₀ h)).comp V)
      =o[𝓝 0] fun h => h := by
    have hlo := hasFDerivAt_iff_isLittleO_nhds_zero.mp hBd
    have hbig : (fun h : X => ((U x₀).comp
        (F.B (b + 1) (x₀ + h) - F.B (b + 1) x₀ - fderiv ℝ (F.B (b + 1)) x₀ h)).comp V) =O[𝓝 0]
        fun h => F.B (b + 1) (x₀ + h) - F.B (b + 1) x₀ - fderiv ℝ (F.B (b + 1)) x₀ h := by
      refine IsBigO.of_bound (‖U x₀‖ * ‖V‖) (Eventually.of_forall fun h => ?_)
      set Δ := F.B (b + 1) (x₀ + h) - F.B (b + 1) x₀ - fderiv ℝ (F.B (b + 1)) x₀ h with hΔ
      calc ‖((U x₀).comp Δ).comp V‖
          ≤ ‖U x₀‖ * ‖Δ‖ * ‖V‖ := by
            refine le_trans (opNorm_comp_le _ _) ?_
            gcongr; exact opNorm_comp_le _ _
        _ = ‖U x₀‖ * ‖V‖ * ‖Δ‖ := by ring
    exact hbig.trans_isLittleO hlo
  have := he₁.sub he₂
  refine this.congr_left fun h => ?_
  exact (hsplit h).symm

/-! ## §4 C^k with loss: the induction -/

/-- The loss budget for C^k: L 0 = 1, L (k+1) = 2·L k + 1 (so L k = 2^(k+1) − 1). -/
def lossBudget : ℕ → ℕ
  | 0 => 1
  | k + 1 => 2 * lossBudget k + 1

theorem one_le_lossBudget (k : ℕ) : 1 ≤ lossBudget k := by
  induction k with
  | zero => simp [lossBudget]
  | succ k ih => simp only [lossBudget]; omega

/-- The differentiated compatibility: incl a b ∘ ∂B a x h = ∂B b x h ∘ incl (a+1) (b+1). -/
theorem fderiv_B_incl_gen (a b : ℕ) (hab : b ≤ a) (x h : X) :
    (S.incl a b hab).comp (fderiv ℝ (F.B a) x h) =
      (fderiv ℝ (F.B b) x h).comp (S.incl (a + 1) (b + 1) (by omega)) := by
  have hBa : HasFDerivAt (F.B a) (fderiv ℝ (F.B a) x) x :=
    ((F.smooth a).differentiable (by simp) x).hasFDerivAt
  have hBb : HasFDerivAt (F.B b) (fderiv ℝ (F.B b) x) x :=
    ((F.smooth b).differentiable (by simp) x).hasFDerivAt
  have h1 : HasFDerivAt (fun y => (S.incl a b hab).comp (F.B a y))
      ((compL ℝ (S.H (a + 1)) (S.H a) (S.H b) (S.incl a b hab)).comp (fderiv ℝ (F.B a) x)) x := by
    have := (compL ℝ (S.H (a + 1)) (S.H a) (S.H b) (S.incl a b hab)).hasFDerivAt.comp x hBa
    simpa [Function.comp_def, compL_apply] using this
  have h2 : HasFDerivAt (fun y => (F.B b y).comp (S.incl (a + 1) (b + 1) (by omega)))
      (((compL ℝ (S.H (a + 1)) (S.H (b + 1)) (S.H b)).flip
        (S.incl (a + 1) (b + 1) (by omega))).comp (fderiv ℝ (F.B b) x)) x := by
    have := ((compL ℝ (S.H (a + 1)) (S.H (b + 1)) (S.H b)).flip
      (S.incl (a + 1) (b + 1) (by omega))).hasFDerivAt.comp x hBb
    simpa [Function.comp_def, compL_apply, flip_apply] using this
  have hfun : (fun y => (S.incl a b hab).comp (F.B a y)) =
      fun y => (F.B b y).comp (S.incl (a + 1) (b + 1) (by omega)) :=
    funext fun y => B_incl_gen F a b hab y
  rw [hfun] at h1
  have := congrArg (fun T => T h) (h1.unique h2)
  simpa [compL_apply, flip_apply] using this

/-- The derivative split at an intermediate level b+j:
−(incl (b+j) b ∘ R (b+j) x) ∘ (∂B (b+j) x h) ∘ (incl a (b+j+1) ∘ R a x). -/
noncomputable def derivSplit (a b j : ℕ) (hj : b + j + 1 ≤ a) (x : X) :
    X →L[ℝ] (S.H a →L[ℝ] S.H b) :=
  -(((compL ℝ (S.H a) (S.H (b + j)) (S.H b))
      ((S.incl (b + j) b (Nat.le_add_right b j)).comp (F.R (b + j) x))).comp
    (((compL ℝ (S.H a) (S.H (b + j + 1)) (S.H (b + j))).flip
      ((S.incl a (b + j + 1) hj).comp (F.R a x))).comp (fderiv ℝ (F.B (b + j)) x)))

/-- Every split equals the level-b canonical form −R b x ∘ ∂B b x h ∘ incl a (b+1) ∘ R a x. -/
theorem derivSplit_apply_canonical (a b j : ℕ) (hj : b + j + 1 ≤ a) (x h : X) :
    derivSplit F a b j hj x h =
      -((F.R b x).comp ((fderiv ℝ (F.B b) x h).comp
        ((S.incl a (b + 1) (by omega)).comp (F.R a x)))) := by
  simp only [derivSplit, neg_apply, coe_comp, Function.comp_apply, compL_apply, flip_apply]
  congr 1
  -- left-associate, then push the inclusions through R and ∂B
  rw [← comp_assoc, ← comp_assoc, R_incl_gen F (b + j) b (Nat.le_add_right b j) x,
    comp_assoc (F.R b x), fderiv_B_incl_gen F (b + j) b (Nat.le_add_right b j) x h,
    comp_assoc (F.R b x), comp_assoc (fderiv ℝ (F.B b) x h), S.incl_trans]
  simp only [comp_assoc]

theorem derivLoss_eq_derivSplit (a b : ℕ) (hab : b + 2 ≤ a) (x : X) :
    derivLoss F a b hab x = derivSplit F a b 1 hab x := rfl

/-- Smoothness of a split derivative from smoothness of its two resolvent factors. -/
theorem contDiff_derivSplit (k : ℕ) (a b j : ℕ) (hj : b + j + 1 ≤ a)
    (hU : ContDiff ℝ k fun x => (S.incl (b + j) b (Nat.le_add_right b j)).comp (F.R (b + j) x))
    (hV : ContDiff ℝ k fun x => (S.incl a (b + j + 1) hj).comp (F.R a x)) :
    ContDiff ℝ k fun x => derivSplit F a b j hj x := by
  have hW : ContDiff ℝ k (fderiv ℝ (F.B (b + j))) := (F.smooth (b + j)).fderiv_right le_top
  have h1 : ContDiff ℝ k fun x => (compL ℝ (S.H a) (S.H (b + j)) (S.H b))
      ((S.incl (b + j) b (Nat.le_add_right b j)).comp (F.R (b + j) x)) :=
    contDiff_const.clm_apply hU
  have h2 : ContDiff ℝ k fun x => (compL ℝ (S.H a) (S.H (b + j + 1)) (S.H (b + j))).flip
      ((S.incl a (b + j + 1) hj).comp (F.R a x)) :=
    contDiff_const.clm_apply hV
  exact (h1.clm_comp (h2.clm_comp hW)).neg

/-- THE THEOREM. On a scale with a locally uniformly bounded resolvent family and a smooth generator
family, the resolvent with loss ≥ L k is C^k in the parameter. -/
theorem contDiff_loss : ∀ (k : ℕ) (a b : ℕ) (hab : b + lossBudget k ≤ a),
    ContDiff ℝ k fun x => (S.incl a b (le_trans (Nat.le_add_right b _) hab)).comp (F.R a x) := by
  intro k
  induction k with
  | zero =>
    intro a b hab
    simp only [Nat.cast_zero, contDiff_zero]
    exact continuous_loss F a b (by simpa [lossBudget] using hab)
  | succ k ih =>
    intro a b hab
    have hL1 := one_le_lossBudget k
    have hab2 : b + 2 ≤ a := by simp only [lossBudget] at hab; omega
    have hd : ∀ x, HasFDerivAt
        (fun x => (S.incl a b (le_trans (Nat.le_add_right b _) hab)).comp (F.R a x))
        (derivLoss F a b hab2 x) x := hasFDerivAt_loss F a b hab2
    rw [Nat.cast_succ, contDiff_succ_iff_fderiv]
    refine ⟨fun x => (hd x).differentiableAt, fun h => absurd h (WithTop.natCast_ne_top k), ?_⟩
    have hj : b + lossBudget k + 1 ≤ a := by simp only [lossBudget] at hab; omega
    have hfd : fderiv ℝ (fun x => (S.incl a b (le_trans (Nat.le_add_right b _) hab)).comp
        (F.R a x)) = fun x => derivSplit F a b (lossBudget k) hj x := by
      funext x
      rw [(hd x).fderiv, derivLoss_eq_derivSplit]
      ext h
      rw [derivSplit_apply_canonical, derivSplit_apply_canonical]
    rw [hfd]
    exact contDiff_derivSplit F k a b (lossBudget k) hj (ih (b + lossBudget k) b le_rfl)
      (ih a (b + lossBudget k + 1) (by simp only [lossBudget] at hab; omega))

end Scale

end FriedCrossing
