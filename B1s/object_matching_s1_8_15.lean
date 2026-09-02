/-
OBJECT MATCHING, S¹ PROTOTYPE (8/15) — obligation #1 of note_preflight_8_15.md.

Source: Bismut, "A survey of the hypoelliptic Laplacian" (Astérisque 322), §1; transcription
seeds in bl_operator_transcription_8_15.md. All identities are stated DENOMINATOR-CLEARED
(multiplied by 2b²) in a Weyl algebra: A any ℝ-algebra, D Y : A with the single relation
  rel : D * Y = Y * D + 1        (i.e. [D,Y] = 1 — D = ∂_y, Y = mult by y).
The Fourier variable ∂_x is a commuting scalar s : ℝ (it is central); b : ℝ is the
deformation parameter. Scalars enter via • (ℝ-algebra structure), always normalized left.

THEOREMS (target: zero sorries; vehicle enters only as docstring interpretation):
  T1 crossSource   — survey (1.8) = (1.9): the transcription cross-check, two printed
                     forms of ℒ_b agree. Guards against copying errors (Kapteyn-pattern).
  T2 factorization — −D² + Y² − 1 = (Y−D)(Y+D): the oscillator's ground energy is 0 with
                     Bismut's "−1" convention (creation/annihilation form).
  T3 uncoupling    — survey (1.10)–(1.12): substituting Y ↦ Y + bs·1 (Bismut's U_b
                     conjugation at symbol level) turns 2b²ℒ_b into oscillator − b²s²,
                     i.e. ℳ_b = H/b² − ½∂ₓ²: the exact-solvability mechanism behind the
                     spectrum ℕ/b² + 2π²k² (1.14) — the same mechanism the S¹ bridge test
                     (s1_bridge_test_8_15.md) probes numerically.
  T4 langevinMatch — THE S¹ GENERATOR IDENTITY: 2b²·(−ℒ_b) equals the fiber-OU Langevin
                     generator with D replaced by D + Y (the ground-state/h-transform
                     substitution e^{y²/2}(·)e^{−y²/2}: D ↦ D − Y, inverted). Vehicle
                     reading: generator(Langevin SDE + FK) = Bismut's operator — the
                     object-matching prototype. The full geometric version (survey (3.24),
                     curvature symbols, form degrees, ⊗F_ρ) is the planned v2.
-/
import Mathlib

namespace FriedObjectMatching

variable {A : Type*} [Ring A] [Algebra ℝ A]
variable (D Y : A)
variable (b s : ℝ)

/-- Survey (1.8), cleared by 2b²:  2b²·ℒ_b = −D² + Y² − 1 − 2bs·Y
(the transport term −(1/b)y∂ₓ contributes −2bs·Y after clearing; s stands for ∂ₓ). -/
noncomputable def L18 : A := -(D * D) + Y * Y - 1 - (2 * b * s) • Y

/-- Survey (1.9), cleared by 2b²:  −D² + (Y − bs)² − 1 − b²s²
(the −½∂ₓ² term contributes −b²s² after clearing). -/
noncomputable def L19 : A :=
  -(D * D) + (Y - (b * s) • 1) * (Y - (b * s) • 1) - 1 - (b ^ 2 * s ^ 2) • 1

/-- T1 (cross-source transcription check): survey (1.8) = (1.9). Commutative content
only — no use of `rel`; a pure convention audit. -/
theorem crossSource : L18 D Y b s = L19 D Y b s := by
  unfold L18 L19
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, mul_one, one_mul]
  module

omit [Algebra ℝ A] in
/-- T2 (ground-energy factorization): −D² + Y² − 1 = (Y − D)(Y + D). Uses `rel` once;
verifies Bismut's "−1" (ground energy 0) convention. -/
theorem factorization (rel : D * Y = Y * D + 1) :
    -(D * D) + Y * Y - 1 = (Y - D) * (Y + D) := by
  have expand : (Y - D) * (Y + D) = Y * Y + Y * D - D * Y - D * D := by noncomm_ring
  rw [expand, rel]
  noncomm_ring

/-- T3 (Bismut's uncoupling, survey (1.10)–(1.12)): substituting Y ↦ Y + bs·1 in 2b²ℒ_b
yields the uncoupled  −D² + Y² − 1 − b²s²  (i.e. ℳ_b = H/b² − ½∂ₓ²). Commutative
content only. -/
theorem uncoupling :
    -(D * D) + (Y + (b * s) • 1) * (Y + (b * s) • 1) - 1
      - (2 * b * s) • (Y + (b * s) • 1)
    = -(D * D) + Y * Y - 1 - (b ^ 2 * s ^ 2) • 1 := by
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul, mul_one, one_mul,
    smul_add]
  module

/-- T4 (THE S¹ GENERATOR IDENTITY — Langevin/h-transform match): substituting the
ground-state twist D' = D + Y into the OU-plus-transport generator ½D'² − Y·D' + bs·Y
(2b²-cleared) gives exactly 2b²·(−ℒ_b). Uses `rel` once. The exact-real (Witten) twist of
twist_taxonomy_citations_8_13.md as a SUBSTITUTION — no measure theory anywhere. -/
theorem langevinMatch (rel : D * Y = Y * D + 1) :
    D * D - Y * Y + 1 + (2 * b * s) • Y
    = (D + Y) * (D + Y) - 2 • (Y * (D + Y)) + (2 * b * s) • Y := by
  have expand : (D + Y) * (D + Y) = D * D + D * Y + Y * D + Y * Y := by noncomm_ring
  have expand2 : Y * (D + Y) = Y * D + Y * Y := by noncomm_ring
  rw [expand, expand2, rel]
  simp only [two_smul]
  noncomm_ring

/-! ## Consistency: the relation `rel` is satisfiable (polynomial model).
D = d/dy on ℝ[y], Y = multiplication by y. Guards the abstract theorems against vacuity. -/

noncomputable def Dop : Module.End ℝ (Polynomial ℝ) :=
  Polynomial.derivative                                -- NAME? (linear-map version)

noncomputable def Yop : Module.End ℝ (Polynomial ℝ) :=
  LinearMap.mulLeft ℝ Polynomial.X

theorem model_rel : Dop * Yop = Yop * Dop + 1 := by
  -- `ext p : 1` picks the monomial-basis extensionality (goal = composition with
  -- `monomial p`, p : ℕ), so the apply-lemmas never fire; take pointwise ext explicitly.
  refine LinearMap.ext fun p => ?_
  simp [Dop, Yop, Module.End.mul_apply, LinearMap.mulLeft_apply, LinearMap.add_apply,
    Module.End.one_apply, Polynomial.derivative_mul, Polynomial.derivative_X]
  ring

end FriedObjectMatching
