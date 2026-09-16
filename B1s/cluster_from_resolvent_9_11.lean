/-
THE CLUSTER MATRICES FROM THE RESOLVENT — input (B) derived (9/11).

Companion to `resolvent_scale_9_11` (which proves: on a Banach scale, a locally uniformly bounded
resolvent family with a smooth generator is C^k with loss). This file goes from there to the
ledger's `ClusterC3`:

  §1  a jointly C^n integrand on a compact interval integrates to a C^n function of the parameter
      (missing from Mathlib; induction on n with dominated differentiation under the integral);
  §2  complex-valued MATRIX ELEMENTS ⟨R(x)φ, ℓ⟩_ℂ := ℓ(Rφ) − i·ℓ(J Rφ) of the resolvent with loss,
      for a fixed vector φ ∈ H a and a fixed real functional ℓ on H b: C³ in the parameter, by the
      scale theorem with loss L 3 = 15;
  §3  the RIESZ PROJECTOR's matrix elements as contour integrals −(1/2πi)∮⟨R(p,λ)φ, ℓ⟩dλ over a
      fixed circle, and the pairing ⟨PΠ̃φ, ℓ⟩ = −(1/2πi)∮ λ⟨R(p,λ)φ, ℓ⟩dλ (since
      P R(λ) = incl + λR(λ)): both C³ in p by §1;
  §4  the FRAME MATRIX: with a frame φ_j and dual functionals ℓ_l, A(p) := (⟨Π̃(p)φ_j, ℓ_l⟩),
      B(p) := (⟨PΠ̃(p)φ_j, ℓ_l⟩), the cluster matrix in the frame Π̃(p)φ_j is M(p) := A(p)⁻¹B(p);
      with det A ≠ 0 its entries are C³; the real cluster matrices of the ledger are the real parts;
  §5  `clusterC3_of_resolvent`: `Ledger.ClusterC3` for two such families (degree 1: 2×2; degree 2:
      4×4).

WHAT IS CITED, WHAT IS DEFINED, WHAT IS DERIVED. The analytic inputs are exactly the fields of
`Scale.ResolventFamily` — local uniform boundedness and the inverse relations (CDDP Lemma 4.3), and
smoothness of the generator in (θ,τ,λ) — for the twisted deformed generator on each level of the
anisotropic scale, pulled back by smooth retractions so as to be globally defined (the resolvent
exists only off the resonance set; the contour is fixed and resonance-free for the parameters in
range, CDDP §4.2). The frame data (φ_j, ℓ_l) and det A ≠ 0 are choices (the dual frame at (0,0),
CP20 §6.2). The matrix M := A⁻¹B is the DEFINITION of "the cluster matrix in the moving frame"; that
it is the matrix of P on Ran Π̃ is the finite-dimensional remark B = A·M when P preserves Ran Π̃,
not formalised here. Its REALITY (imaginary part zero) is the cluster's conjugation symmetry — a
separate ledger fact. Everything else — every derivative — is proved.

⚡AUDIT CRITERION: ZERO axioms of its own — `#print axioms` on every theorem = built-ins only.
-/
import B1s.resolvent_scale_9_11
import B1s.fried_cluster_matrices_9_10

set_option linter.style.header false

namespace FriedCrossing

open Filter Topology ContinuousLinearMap MeasureTheory intervalIntegral Scale

/-! ## §1 Parametric interval integrals of jointly C^n integrands are C^n -/
namespace ParamInt

/-- The partial derivative in the parameter of a two-variable function, as a CLM. -/
noncomputable def partialX {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (F : E → ℝ → G) (x : E) (t : ℝ) : E →L[ℝ] G :=
  (fderiv ℝ (Function.uncurry F) (x, t)).comp (inl ℝ E ℝ)

theorem contDiff_uncurry_partialX {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (F : E → ℝ → G) (n : ℕ)
    (hF : ContDiff ℝ (n + 1) (Function.uncurry F)) :
    ContDiff ℝ n (Function.uncurry (partialX F)) := by
  have : Function.uncurry (partialX F) = fun q : E × ℝ =>
      (fderiv ℝ (Function.uncurry F) q).comp (inl ℝ E ℝ) := by
    funext q; rfl
  rw [this]
  exact (hF.fderiv_right le_rfl).clm_comp contDiff_const

theorem hasFDerivAt_partialX {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (F : E → ℝ → G) (n : ℕ)
    (hF : ContDiff ℝ (n + 1) (Function.uncurry F)) (x : E) (t : ℝ) :
    HasFDerivAt (fun x => F x t) (partialX F x t) x := by
  have h1 : HasFDerivAt (Function.uncurry F) (fderiv ℝ (Function.uncurry F) (x, t)) (x, t) :=
    ((hF.differentiable (by simp)) (x, t)).hasFDerivAt
  have h2 : HasFDerivAt (fun x : E => ((x, t) : E × ℝ)) (inl ℝ E ℝ) x := hasFDerivAt_prodMk_left x t
  exact h1.comp x h2

/-- THE LEMMA. A jointly C^n integrand on a fixed compact interval integrates to a C^n function of
a finite-dimensional parameter. Induction on n; differentiation under the integral is dominated by
a constant from compactness of a closed ball times the interval. -/
theorem contDiff_parametric_intervalIntegral {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] (a b : ℝ) :
    ∀ (n : ℕ) (G : Type) [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
      (F : E → ℝ → G), ContDiff ℝ n (Function.uncurry F) →
      ContDiff ℝ n fun x => ∫ t in a..b, F x t := by
  intro n
  induction n with
  | zero =>
    intro G _ _ _ F hF
    simp only [Nat.cast_zero, contDiff_zero] at hF ⊢
    exact continuous_parametric_intervalIntegral_of_continuous' hF a b
  | succ n ih =>
    intro G _ _ _ F hF
    have hcont : Continuous (Function.uncurry F) := hF.continuous
    have hF' := contDiff_uncurry_partialX F n hF
    have hF'cont : Continuous (Function.uncurry (partialX F)) := hF'.continuous
    -- differentiability at every x₀, with derivative ∫ ∂ₓF
    have hd : ∀ x₀ : E, HasFDerivAt (fun x => ∫ t in a..b, F x t)
        (∫ t in a..b, partialX F x₀ t) x₀ := by
      intro x₀
      -- a bound on ‖∂ₓF‖ over the compact set closedBall x₀ 1 × uIcc a b
      have hK : IsCompact (Metric.closedBall x₀ 1 ×ˢ Set.uIcc a b) :=
        (isCompact_closedBall x₀ 1).prod isCompact_uIcc
      obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF'cont.continuousOn
      refine hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume) (bound := fun _ => C)
        (s := Metric.ball x₀ 1) (Metric.ball_mem_nhds x₀ one_pos) ?_ ?_ ?_ ?_ ?_ ?_
      · exact Eventually.of_forall fun x =>
          (hcont.comp (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable
      · exact (hcont.comp (Continuous.prodMk continuous_const continuous_id)).intervalIntegrable a b
      · exact (hF'cont.comp (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable
      · refine Eventually.of_forall fun t ht x hx => ?_
        exact hC (x, t) ⟨Metric.ball_subset_closedBall hx, Set.uIoc_subset_uIcc ht⟩
      · exact intervalIntegrable_const
      · exact Eventually.of_forall fun t _ x _ => hasFDerivAt_partialX F n hF x t
    rw [Nat.cast_succ, contDiff_succ_iff_fderiv]
    refine ⟨fun x => (hd x).differentiableAt, fun h => absurd h (WithTop.natCast_ne_top n), ?_⟩
    have hfd : fderiv ℝ (fun x => ∫ t in a..b, F x t) = fun x => ∫ t in a..b, partialX F x t := by
      funext x; exact (hd x).fderiv
    rw [hfd]
    exact ih (E →L[ℝ] G) (partialX F) hF'

end ParamInt

/-! ## §2 Complex structure and matrix elements of the resolvent with loss -/
namespace ClusterFrame

open ParamInt

variable {S : BanachScale.{0}} (F : ResolventFamily S Param) (Jc : ComplexStructure S)

/-- Matrix elements of the resolvent with loss ≥ L 3 = 15 are C³ in (θ, τ, λ). -/
theorem contDiff_melem (a b : ℕ) (hab : b + 15 ≤ a) (φ : S.H a) (ℓ : S.H b →L[ℝ] ℝ) :
    ContDiff ℝ 3 (melem F Jc a b (by omega) φ ℓ) := by
  have hT : ContDiff ℝ 3 fun x => (S.incl a b (by omega)).comp (F.R a x) :=
    contDiff_loss F 3 a b (by simpa [lossBudget] using hab)
  have h1 : ContDiff ℝ 3 fun x => ℓ (((S.incl a b (by omega)).comp (F.R a x)) φ) :=
    contDiff_const.clm_apply (hT.clm_apply contDiff_const)
  have h2 : ContDiff ℝ 3 fun x => ℓ (Jc.J b (((S.incl a b (by omega)).comp (F.R a x)) φ)) :=
    contDiff_const.clm_apply (contDiff_const.clm_apply (hT.clm_apply contDiff_const))
  unfold melem
  exact (Complex.ofRealCLM.contDiff.comp h1).sub
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp h2))

/-! ## §3 Contour integrals: the Riesz projector's matrix elements -/

theorem contDiff_contour (c : ℂ) (r : ℝ) : ContDiff ℝ ⊤ fun t : ℝ => contour c r t := by
  unfold contour
  refine contDiff_const.add (contDiff_const.mul (Complex.contDiff_exp.comp ?_))
  exact contDiff_const.mul Complex.ofRealCLM.contDiff

/-- A C³ function of (p, λ) has C³ contour integrals in p. -/
theorem contDiff_riesz (c : ℂ) (r : ℝ) (g : Param → ℂ) (hg : ContDiff ℝ 3 g) :
    ContDiff ℝ 3 (riesz c r g) := by
  have hint : ContDiff ℝ 3 (Function.uncurry fun (p : ℝ × ℝ) (t : ℝ) =>
      g (p, contour c r t) * Complex.exp (Complex.I * t)) := by
    have hγ : ContDiff ℝ 3 fun q : (ℝ × ℝ) × ℝ => ((q.1, contour c r q.2) : Param) :=
      contDiff_fst.prodMk ((contDiff_contour c r).of_le le_top |>.comp contDiff_snd)
    have he : ContDiff ℝ 3 fun q : (ℝ × ℝ) × ℝ => Complex.exp (Complex.I * (q.2 : ℂ)) :=
      Complex.contDiff_exp.of_le le_top |>.comp
        (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp contDiff_snd))
    exact (hg.comp hγ).mul he
  unfold riesz
  exact contDiff_const.mul
    (contDiff_parametric_intervalIntegral (0 : ℝ) (2 * Real.pi) 3 ℂ _ hint)

/-! ## §4 The frame matrix and its regularity -/

variable {k : ℕ}

theorem contDiff_Amat (D : FrameData S k) (l j : Fin k) :
    ContDiff ℝ 3 fun p => Amat F Jc D p l j := by
  simp only [Amat, Matrix.of_apply]
  exact contDiff_riesz _ _ _ (contDiff_melem F Jc D.a D.b D.hab (D.φ j) (D.ℓ l))

theorem contDiff_Bmat (D : FrameData S k) (l j : Fin k) :
    ContDiff ℝ 3 fun p => Bmat F Jc D p l j := by
  simp only [Bmat, Matrix.of_apply]
  refine contDiff_riesz _ _ _ ?_
  exact (contDiff_snd).mul (contDiff_melem F Jc D.a D.b D.hab (D.φ j) (D.ℓ l))

/-- Determinants of ℂ-matrices with C^n entries (real smoothness). -/
theorem contDiff_det_complex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : Type*} [Fintype n] [DecidableEq n] {m : WithTop ℕ∞} {A : E → Matrix n n ℂ}
    (h : ∀ i j, ContDiff ℝ m fun x => A x i j) : ContDiff ℝ m fun x => (A x).det := by
  simp only [Matrix.det_apply']
  exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => h _ _)

theorem contDiff_adjugate_complex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : Type*} [Fintype n] [DecidableEq n] {m : WithTop ℕ∞} {A : E → Matrix n n ℂ}
    (h : ∀ i j, ContDiff ℝ m fun x => A x i j) (i j : n) :
    ContDiff ℝ m fun x => (A x).adjugate i j := by
  simp only [Matrix.adjugate_apply]
  refine contDiff_det_complex fun i' j' => ?_
  rcases eq_or_ne i' j with rfl | hne
  · simp only [Matrix.updateRow_self]; exact contDiff_const
  · simp only [Matrix.updateRow_ne hne]; exact h i' j'

/-- Entries of the inverse of a nonsingular C^m matrix family are C^m. -/
theorem contDiff_inv_complex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : Type*} [Fintype n] [DecidableEq n] {m : WithTop ℕ∞} {A : E → Matrix n n ℂ}
    (h : ∀ i j, ContDiff ℝ m fun x => A x i j) (hdet : ∀ x, (A x).det ≠ 0) (i j : n) :
    ContDiff ℝ m fun x => (A x)⁻¹ i j := by
  have : (fun x => (A x)⁻¹ i j) = fun x => ((A x).det)⁻¹ * (A x).adjugate i j := by
    funext x
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  rw [this]
  exact ((contDiff_det_complex h).inv hdet).mul (contDiff_adjugate_complex h i j)

/-- Entries of a product of C^m matrix families are C^m. -/
theorem contDiff_mul_complex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : Type*} [Fintype n] {m : WithTop ℕ∞} {A B : E → Matrix n n ℂ}
    (hA : ∀ i j, ContDiff ℝ m fun x => A x i j) (hB : ∀ i j, ContDiff ℝ m fun x => B x i j)
    (i j : n) : ContDiff ℝ m fun x => (A x * B x) i j := by
  simp only [Matrix.mul_apply]
  exact ContDiff.sum fun l _ => (hA i l).mul (hB l j)

/-- THE FRAME MATRIX IS C³ (given the frame is nondegenerate). -/
theorem contDiff_Mframe (D : FrameData S k) (hdet : ∀ p, (Amat F Jc D p).det ≠ 0) (l j : Fin k) :
    ContDiff ℝ 3 fun p => Mframe F Jc D p l j := by
  unfold Mframe
  exact contDiff_mul_complex (fun i j => contDiff_inv_complex (contDiff_Amat F Jc D) hdet i j)
    (contDiff_Bmat F Jc D) l j

/-! ## §5 The ledger's input (B) -/

theorem contDiff_Mreal (D : FrameData S k) (hdet : ∀ p, (Amat F Jc D p).det ≠ 0) (i j : Fin k) :
    ContDiff ℝ 3 fun q : ℝ × ℝ => Mreal F Jc D q.1 q.2 i j := by
  have : (fun q : ℝ × ℝ => Mreal F Jc D q.1 q.2 i j) =
      fun q : ℝ × ℝ => Complex.reCLM (Mframe F Jc D q i j) := by
    funext q; simp [Mreal, Matrix.map_apply]
  rw [this]
  exact Complex.reCLM.contDiff.comp (contDiff_Mframe F Jc D hdet i j)

/-- INPUT (B) DERIVED: two resolvent families (degree 1 on its scale, degree 2 on its scale), each
with a nondegenerate frame, give `Ledger.ClusterC3` for the real frame matrices. -/
theorem clusterC3_of_resolvent {S₁ S₂ : BanachScale.{0}}
    (F₁ : ResolventFamily S₁ Param) (J₁ : ComplexStructure S₁) (D₁ : FrameData S₁ 2)
    (F₂ : ResolventFamily S₂ Param) (J₂ : ComplexStructure S₂) (D₂ : FrameData S₂ 4)
    (hdet₁ : ∀ p, (Amat F₁ J₁ D₁ p).det ≠ 0) (hdet₂ : ∀ p, (Amat F₂ J₂ D₂ p).det ≠ 0) :
    Ledger.ClusterC3 (Mreal F₁ J₁ D₁) (Mreal F₂ J₂ D₂) where
  deg1 i j := contDiff_Mreal F₁ J₁ D₁ hdet₁ i j
  deg2 i j := contDiff_Mreal F₂ J₂ D₂ hdet₂ i j

end ClusterFrame

end FriedCrossing
