/-
fried_statement_defs_9_14 — every DEFINITION that appears in the type of the statement theorem
`fried_counterexample_of_resolvent_inputs`, in one module, in one fixed order.

WHY ONE MODULE (9/14, Palomar): `leanprover/comparator` compares each constant in the statement's
closure BY VALUE between the Mathlib-only `Challenge.lean` and the development. When Lean elaborates
a real numeral such as the `2` in `/ 2`, the `Nat.AtLeastTwo` instance is a proof, and Lean lifts it
into a hidden auxiliary lemma (`<firstOwner>._proof_1`) that is cached PER MODULE and reused by every
later definition in that module needing the same proof. With the definitions spread over seven leg
files, `hq'` owned its own copy in the development but reused `wPlus`'s in the single-file
Challenge, and comparator rejected the pair. Keeping every statement definition here, and
generating `Challenge.lean` from this file verbatim (`scripts/make_challenge.py`), makes both
environments build the same cache in the same order.

RULES. (1) The ORDER of declarations here is load-bearing; append, never reorder. (2) No theorems
here: proofs live in the leg files, which import this module. (3) After editing, regenerate the
Challenge (`python3 scripts/make_challenge.py`) and rerun comparator. (4) Each leg file's header
still documents its definitions' mathematics; the docstrings here are the audit surface a Palomar
reader sees.

Sources named in docstrings: CDDP = Cekić–Delarue–Dyatlov–Paternain, DGRS = Dang–Guillarmou–
Rivière–Shen, BuOl = Bunke–Olbrich, CD = Chaubet–Dang, DR = Dang–Rivière.
-/
import Mathlib

set_option linter.style.header false

namespace FriedCrossing

open Filter Topology Matrix

/-! ## Torsion of the zero cluster (CD Def 3.2) — leg `fried_crossing_9_03` -/

namespace TorsionCore

variable {K : Type*} [Field K]

/-- d₁ : C¹ → C², u ↦ (Xu, d₀u) = (0, w₁). -/
def d₁ : Matrix (Fin 3) (Fin 1) K := !![0; 1; 0]

/-- d₂ : C² → C³ for the (x, l)-cluster: α∧u ↦ −α∧w₁ + Lu, w₁ ↦ 0,
w₂ ↦ x·α∧w₁ + l·Lu (columns in the C²-basis, rows in the C³-basis). -/
def d₂ (x l : K) : Matrix (Fin 3) (Fin 3) K := !![-1, 0, x; 0, 0, 0; 1, 0, l]

/-- d₃ : C³ → C⁴: α∧w₁ ↦ 0, α∧w₂ ↦ −l·α∧Lu, Lu ↦ 0. -/
def d₃ (l : K) : Matrix (Fin 1) (Fin 3) K := !![0, -l, 0]

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

/-- CD Def 3.2 sign exponent N(C^•) = ½ Σ_j dim A^j (dim A^j + (−1)^{j+1}) for the
complement dimensions (1, 2, 1, 0) in degrees 1..4: ½(1·2 + 2·1 + 1·2 + 0) = 3. -/
def N_C : ℕ := 3

/-- CD Def 3.2 chirality-element sign exponent m(C^•) = ½ Σ_{j≤r} dim C^j (dim C^j +
(−1)^{r+j}), r = 2, dims (0, 1, 3): ½(0 + 1·0 + 3·4) = 6. -/
def m_C : ℕ := 6

/-- The refined torsion τ(C^•, Γ_ϑ) of the (x, l)-cluster in CD's normalisation
(Def 3.2 with λ_j = D_j⁻¹, c_j = λ_j·μ(∂a_{j−1} ⊗ a_j)): τ = (−1)^{N+m} ∏ λ_j^{(−1)^j}
= (−1)^{N_C+m_C} · D₁ · D₂⁻¹ · D₃ · D₄⁻¹ with D₁ = det [u] = 1. The Γ_ϑ-basis signs in
c_Γ cancel pairwise (zero_cluster_torsion_9_02 §2.3, validated against CD Prop 6.2). -/
def refinedTorsion (x l : K) : K :=
  (-1) ^ (N_C + m_C) *
    ((!![(1 : K)]).det * (D₂mat : Matrix (Fin 3) (Fin 3) K).det⁻¹ * (D₃mat x l).det *
      (D₄mat l).det⁻¹)

end TorsionCore

namespace OrderCount

/-- CD (5.9) footnote 5 with q = 2: the order of ζ at a resonance is
Σ_k (−1)^k dim C₀^k (degrees 0,2,4 zeros, degrees 1,3 poles). -/
def zetaOrder (c : Fin 5 → ℕ) : ℤ := ∑ k : Fin 5, (-1 : ℤ) ^ (k : ℕ) * (c k : ℤ)

end OrderCount

/-! ## The twin branch and its rate — leg `fried_crossing_rate_9_07` -/

namespace TwinRate

/-- Discriminant of w² − a·w + b. -/
def disc (a b : ℝ) : ℝ := a ^ 2 - 4 * b

/-- The root of w² − a·w + b that sits at r₀ when (a, b) = (r₀, 0), r₀ > 0. -/
noncomputable def wPlus (a b : ℝ) : ℝ := (a + Real.sqrt (disc a b)) / 2

/-- The other root (at 0 when (a, b) = (r₀, 0)): the closed state's first-order rate. -/
noncomputable def wMinus (a b : ℝ) : ℝ := (a - Real.sqrt (disc a b)) / 2

/-- The twin branch s_nc(θ,τ) = s*(θ) + τ·w₊(a(θ,τ), b(θ,τ)). -/
noncomputable def twin (sStar : ℝ → ℝ) (a b : ℝ → ℝ → ℝ) (θ τ : ℝ) : ℝ :=
  sStar θ + τ * wPlus (a θ τ) (b θ τ)

/-- ∂w₊/∂τ given a' = ∂_τa, b' = ∂_τb, where the discriminant is positive. -/
noncomputable def dwPlus (a b a' b' : ℝ) : ℝ :=
  (a' + (2 * a * a' - 4 * b') / (2 * Real.sqrt (disc a b))) / 2

/-- ∂_τ(twin) = w₊ + τ·∂_τw₊. -/
noncomputable def dtwin (a b a' b' τ : ℝ) : ℝ := wPlus a b + τ * dwPlus a b a' b'

end TwinRate

/-! ## CDDP's first variation (4.22) and the Hadamard quotient — leg
`fried_crossing_firstvariation_9_08` -/

namespace FirstVariation

variable {K : Type*} [Field K]

/-- The pairing B(u, u*) = ∫α∧dα∧u∧u* on Res¹₀ × Res¹₀* in the bases (c, ψ), (c*, ψ*). -/
def Bmat (Bcc Bcψ Bψc Bψψ : K) : Matrix (Fin 2) (Fin 2) K := !![Bcc, Bcψ; Bψc, Bψψ]

/-- CDDP (4.22): the matrix of ∂_τZ(0) in the pairing; the c-row and c-column vanish (dc = 0),
p = −i⟨⟨(ι_Xβ)dψ, dψ*⟩⟩ up to the convention factor. -/
def Pmat (p : K) : Matrix (Fin 2) (Fin 2) K := !![0, 0; 0, p]

end FirstVariation

namespace Hadamard

/-- The τ-divided matrix: N(θ,τ) = (M(θ,τ) − s*(θ)·1)/τ for τ ≠ 0, ∂_τM(θ,0) at τ = 0. -/
noncomputable def Ndiv (M M' : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (sStar : ℝ → ℝ)
    (θ τ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  if τ = 0 then M' θ 0 else (1 / τ) • (M θ τ - sStar θ • (1 : Matrix (Fin 2) (Fin 2) ℝ))

end Hadamard

/-! ## The cluster matrices as primitives — leg `fried_cluster_matrices_9_10` -/

namespace ClusterMatrix

/-- Coefficients of the characteristic polynomial of a 4×4 matrix in the quartic normal form
z⁴ − c₁z³ + c₂z² − c₃z + c₄ (c₁ = trace, c₄ = det). -/
noncomputable def c₁ (A : Matrix (Fin 4) (Fin 4) ℝ) : ℝ := -A.charpoly.coeff 3
noncomputable def c₂ (A : Matrix (Fin 4) (Fin 4) ℝ) : ℝ := A.charpoly.coeff 2
noncomputable def c₃ (A : Matrix (Fin 4) (Fin 4) ℝ) : ℝ := -A.charpoly.coeff 1
noncomputable def c₄ (A : Matrix (Fin 4) (Fin 4) ℝ) : ℝ := A.charpoly.coeff 0

/-- The pure quadratic's coefficients from the two cluster matrices:
e₁ = c₁(A) − tr M, e₂ = c₂(A) − det M − (tr M)·e₁. -/
noncomputable def E₁ (A : Matrix (Fin 4) (Fin 4) ℝ) (M : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  c₁ A - M.trace
noncomputable def E₂ (A : Matrix (Fin 4) (Fin 4) ℝ) (M : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  c₂ A - M.det - M.trace * E₁ A M

end ClusterMatrix

namespace Regularity

/-- τ-partial and θ-partial of a two-variable real function. -/
noncomputable def pτ (f : ℝ → ℝ → ℝ) (θ τ : ℝ) : ℝ := deriv (fun t => f θ t) τ
noncomputable def pθ (f : ℝ → ℝ → ℝ) (θ τ : ℝ) : ℝ := deriv (fun s => f s τ) θ

end Regularity

namespace HQuot

/-- q(τ) = (f(τ) − f(0))/τ, q(0) = f'(0). -/
noncomputable def hq (f f' : ℝ → ℝ) (τ : ℝ) : ℝ := if τ = 0 then f' 0 else (f τ - f 0) / τ

/-- Its derivative: (τf'(τ) − (f(τ) − f(0)))/τ² for τ ≠ 0, f''(0)/2 at 0. -/
noncomputable def hq' (f f' f'' : ℝ → ℝ) (τ : ℝ) : ℝ :=
  if τ = 0 then f'' 0 / 2 else (τ * f' τ - (f τ - f 0)) / τ ^ 2

end HQuot

namespace Ledger

/-- PINNING at ρ_triv (θ = 0), on the matrices: the degree-1 cluster has a zero eigenvalue for
every τ (the harmonic 1-form, b₁ = 1), and the degree-2 cluster spectrum is {0, 0, 0, twin} —
0 with multiplicity b₁ + 2 = 3 (CDDP Cor 4.1) and the fourth eigenvalue the lifted twin d₀u_nc
(DGRS Lemma 7.1), whose value is tr M(0,τ) because the other degree-1 eigenvalue is 0. -/
structure Pinned (M : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (A : ℝ → ℝ → Matrix (Fin 4) (Fin 4) ℝ) : Prop where
  deg1 : ∀ τ, (M 0 τ).det = 0
  deg2 : ∀ τ z, (A 0 τ).charpoly.eval z = z ^ 3 * (z - (M 0 τ).trace)

/-- CHAUBET–DANG (6.5) at λ = 0 along the family (9/11). Near a crossing of the twin s, ζ factors
through the zero cluster: ζ(λ; g_τ) = F(λ,τ)·(λ − z(τ))/(λ − s(τ)) with F holomorphic, nonvanishing
and continuous in τ. Read at λ = 0 with ζ₀(τ) := ζ(0; g_τ) and F(τ) := F(0,τ): off the crossing
ζ₀ = F·z/s (`off`); F is continuous at each crossing (`cont`); AT the crossing z = s = 0, the factor
is λ/λ = 1 and ζ₀(σ) = F(σ) (`at_crossing`). This is the single fact formerly split into
`hregular` and the shape of `hfried_off`. -/
structure ZetaFactorization (ζ₀ F s z : ℝ → ℝ) (δ : ℝ) : Prop where
  off : ∀ τ, |τ| < δ → s τ ≠ 0 → ζ₀ τ = F τ * z τ / s τ
  cont : ∀ τ₀, s τ₀ = 0 → ContinuousAt F τ₀
  at_crossing : ∀ τ₀, s τ₀ = 0 → ζ₀ τ₀ = F τ₀

end Ledger

namespace Derived

open Regularity HQuot Hadamard ClusterMatrix Ledger

/-- ∂_τM and ∂²_τM, entrywise. -/
noncomputable def Mτ (M : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (θ τ : ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => pτ (fun θ τ => M θ τ i j) θ τ

noncomputable def Mττ (M : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (θ τ : ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => pτ (fun θ τ => Mτ M θ τ i j) θ τ

/-- The entrywise derivative of N = `Ndiv` (the Hadamard quotient), and the derivatives of its
trace and determinant. -/
noncomputable def Nτ (M : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (θ τ : ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j =>
    hq' (fun t => M θ t i j) (fun t => Mτ M θ t i j) (fun t => Mττ M θ t i j) τ

noncomputable def aτ (M : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (θ τ : ℝ) : ℝ := (Nτ M θ τ).trace

noncomputable def bτ (M : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (sStar : ℝ → ℝ) (θ τ : ℝ) : ℝ :=
  Nτ M θ τ 0 0 * Ndiv M (Mτ M) sStar θ τ 1 1 + Ndiv M (Mτ M) sStar θ τ 0 0 * Nτ M θ τ 1 1 -
    (Nτ M θ τ 0 1 * Ndiv M (Mτ M) sStar θ τ 1 0 + Ndiv M (Mτ M) sStar θ τ 0 1 * Nτ M θ τ 1 0)

/-- The pure quadratic's coefficients as functions of (θ,τ). -/
noncomputable def E₁f (M : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (A : ℝ → ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (θ τ : ℝ) : ℝ := E₁ (A θ τ) (M θ τ)

noncomputable def E₂f (M : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (A : ℝ → ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (θ τ : ℝ) : ℝ := E₂ (A θ τ) (M θ τ)

/-- (9/11) The zero clusters as CONCRETE subspaces: C₀¹, C₀² = the generalized 0-eigenspaces of
the degree-1 and degree-2 cluster matrices (the ranges of the Riesz projectors at 0). Their
dimensions are the algebraic multiplicities of 0 — a Mathlib theorem, no longer the row `hriesz`. -/
noncomputable def resZero₁ (M : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (θ τ : ℝ) :
    Submodule ℝ (Fin 2 → ℝ) := Module.End.maxGenEigenspace (Matrix.toLin' (M θ τ)) 0

noncomputable def resZero₂ (A : ℝ → ℝ → Matrix (Fin 4) (Fin 4) ℝ) (θ τ : ℝ) :
    Submodule ℝ (Fin 4 → ℝ) := Module.End.maxGenEigenspace (Matrix.toLin' (A θ τ)) 0

end Derived

namespace Branch

open TwinRate

/-- The pure degree-2 zero nearest 0: of the two roots w± of Q(τ; ·) = z² − e₁(τ)z + e₂(τ),
the one of smaller modulus. No reference to the crossing is needed: at a crossing Q has the
simple root 0 and the other root e₁(σ) ≠ 0, so this selection is the branch through 0 and is
continuous there. -/
noncomputable def zBranch (e₁ e₂ : ℝ → ℝ) (τ : ℝ) : ℝ :=
  if |wPlus (e₁ τ) (e₂ τ)| ≤ |wMinus (e₁ τ) (e₂ τ)| then wPlus (e₁ τ) (e₂ τ)
  else wMinus (e₁ τ) (e₂ τ)

end Branch

end FriedCrossing

/-! ## Input (B): resolvent families on a Banach scale — leg `resolvent_scale_9_11` -/

namespace FriedCrossing

open Filter Topology ContinuousLinearMap Asymptotics

namespace Scale

universe u

/-- A scale of real Banach spaces `H 0 ⊇ H 1 ⊇ H 2 ⊇ …` with coherent continuous inclusions. -/
structure BanachScale where
  H : ℕ → Type u
  [normed : ∀ n, NormedAddCommGroup (H n)]
  [space : ∀ n, NormedSpace ℝ (H n)]
  [complete : ∀ n, CompleteSpace (H n)]
  incl : ∀ (a b : ℕ), b ≤ a → (H a →L[ℝ] H b)
  incl_refl : ∀ a, incl a a le_rfl = ContinuousLinearMap.id ℝ (H a)
  incl_trans : ∀ a b c (hab : b ≤ a) (hbc : c ≤ b),
    (incl b c hbc).comp (incl a b hab) = incl a c (le_trans hbc hab)

attribute [instance] BanachScale.normed BanachScale.space BanachScale.complete

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A resolvent family on a scale: `R n x` inverts the generator `B n x : H (n+1) → H n` up to the
inclusion, on every level; `R` is bounded locally uniformly in the parameter (CDDP Lemma 4.3); the
generator family is smooth in the parameter and compatible with the inclusions. -/
structure ResolventFamily (S : BanachScale.{u}) (X : Type*) [NormedAddCommGroup X]
    [NormedSpace ℝ X] where
  R : ∀ n, X → (S.H n →L[ℝ] S.H n)
  B : ∀ n, X → (S.H (n + 1) →L[ℝ] S.H n)
  /-- CDDP Lemma 4.3: the resolvent is bounded locally uniformly in the parameter, on each level. -/
  bdd : ∀ n (x₀ : X), ∃ C, ∀ᶠ x in 𝓝 x₀, ‖R n x‖ ≤ C
  /-- the generator family is smooth in the parameter (affine in θ and λ, smooth in τ). -/
  smooth : ∀ n, ContDiff ℝ ⊤ (B n)
  /-- the resolvent is a two-sided inverse of the generator, modulo the inclusion. -/
  inv_left : ∀ n x, (R n x).comp (B n x) = S.incl (n + 1) n (Nat.le_succ n)
  inv_right : ∀ n x, (B n x).comp (R (n + 1) x) = S.incl (n + 1) n (Nat.le_succ n)
  /-- the resolvent commutes with the inclusion. -/
  R_incl : ∀ n x, (S.incl (n + 1) n (Nat.le_succ n)).comp (R (n + 1) x) =
    (R n x).comp (S.incl (n + 1) n (Nat.le_succ n))
  /-- so does the generator. -/
  B_incl : ∀ n x, (S.incl (n + 1) n (Nat.le_succ n)).comp (B (n + 1) x) =
    (B n x).comp (S.incl (n + 2) (n + 1) (Nat.le_succ _))

end Scale

end FriedCrossing

/-! ## The cluster matrices from the resolvent — leg `cluster_from_resolvent_9_11` -/

namespace FriedCrossing

open Filter Topology ContinuousLinearMap MeasureTheory intervalIntegral Scale

namespace ClusterFrame

/-- The parameter space: (θ, τ) ∈ ℝ × ℝ and λ ∈ ℂ, as one real normed space. -/
abbrev Param : Type := (ℝ × ℝ) × ℂ

/-- A complex structure on the scale: J n with J² = −1, commuting with the inclusions. Only its
existence as a bounded operator is used for regularity; the axioms fix the interpretation of the
complex pairing ⟨u, ℓ⟩ := ℓ(u) − i·ℓ(Ju). -/
structure ComplexStructure (S : BanachScale.{0}) where
  J : ∀ n, S.H n →L[ℝ] S.H n
  J_sq : ∀ n, (J n).comp (J n) = -ContinuousLinearMap.id ℝ (S.H n)
  J_incl : ∀ n, (S.incl (n + 1) n (Nat.le_succ n)).comp (J (n + 1)) =
    (J n).comp (S.incl (n + 1) n (Nat.le_succ n))

variable {S : BanachScale.{0}} (F : ResolventFamily S Param) (Jc : ComplexStructure S)

/-- The complex matrix element ⟨(incl a b ∘ R a x) φ, ℓ⟩_ℂ = ℓ(Tφ) − i·ℓ(J(Tφ)). -/
noncomputable def melem (a b : ℕ) (hab : b ≤ a) (φ : S.H a) (ℓ : S.H b →L[ℝ] ℝ) (x : Param) : ℂ :=
  (ℓ (((S.incl a b hab).comp (F.R a x)) φ) : ℂ) -
    Complex.I * (ℓ (Jc.J b (((S.incl a b hab).comp (F.R a x)) φ)) : ℂ)

/-- The fixed contour γ(t) = c + r·e^{it}, t ∈ [0, 2π]. -/
noncomputable def contour (c : ℂ) (r t : ℝ) : ℂ := c + r * Complex.exp (Complex.I * t)

/-- −(1/2πi)∮_γ g(p, λ) dλ = −(r/2π) ∫₀^{2π} g(p, γ(t)) e^{it} dt. -/
noncomputable def riesz (c : ℂ) (r : ℝ) (g : Param → ℂ) (p : ℝ × ℝ) : ℂ :=
  -((r : ℂ) / (2 * Real.pi)) *
    ∫ t in (0 : ℝ)..(2 * Real.pi), g (p, contour c r t) * Complex.exp (Complex.I * t)

/-- Frame data for a rank-k cluster: k vectors φ_j at level a and k real functionals ℓ_l at level
b ≤ a − 15. -/
structure FrameData (S : BanachScale.{0}) (k : ℕ) where
  a : ℕ
  b : ℕ
  hab : b + 15 ≤ a
  φ : Fin k → S.H a
  ℓ : Fin k → (S.H b →L[ℝ] ℝ)
  c : ℂ
  r : ℝ

variable {k : ℕ}

/-- A(p)_{lj} = ⟨Π̃(p) φ_j, ℓ_l⟩ — the Gram-type matrix of the moving frame against the fixed dual
frame. -/
noncomputable def Amat (D : FrameData S k) (p : ℝ × ℝ) : Matrix (Fin k) (Fin k) ℂ :=
  Matrix.of fun l j =>
    riesz D.c D.r (melem F Jc D.a D.b (by have := D.hab; omega) (D.φ j) (D.ℓ l)) p

/-- B(p)_{lj} = ⟨P(p) Π̃(p) φ_j, ℓ_l⟩ = −(1/2πi)∮ λ ⟨R(p,λ)φ_j, ℓ_l⟩ dλ, using
P R(λ) = incl + λ R(λ). -/
noncomputable def Bmat (D : FrameData S k) (p : ℝ × ℝ) : Matrix (Fin k) (Fin k) ℂ :=
  Matrix.of fun l j => riesz D.c D.r
    (fun x => x.2 * melem F Jc D.a D.b (by have := D.hab; omega) (D.φ j) (D.ℓ l) x) p

/-- THE CLUSTER MATRIX IN THE MOVING FRAME: M(p) := A(p)⁻¹ B(p). -/
noncomputable def Mframe (D : FrameData S k) (p : ℝ × ℝ) : Matrix (Fin k) (Fin k) ℂ :=
  (Amat F Jc D p)⁻¹ * Bmat F Jc D p

/-- The real cluster matrix: the real part of the frame matrix (its imaginary part vanishes by the
cluster's conjugation symmetry — a separate ledger fact, not used for regularity). -/
noncomputable def Mreal (D : FrameData S k) (θ τ : ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  (Mframe F Jc D (θ, τ)).map Complex.re

end ClusterFrame

end FriedCrossing

/-! ## The two hypothesis bundles kept with the statement — `fried_counterexample_main` -/

namespace FriedCrossing

open FirstVariation

namespace Ledger

/-- CDDP (4.22): in the basis (c, ψ) of Res¹₀ with pairing B (invertible, Lemmas 2.2 + 2.10), the
first-variation matrix ∂_τM(0,0) solves B·∂_τM(0,0) = P = !![0,0;0,p] — the c-row and c-column
vanish because dc = 0, and p is the (4.22) pairing of the non-closed state (with (4.38)). -/
structure FirstVariation422 (M' : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (Bcc Bcψ Bψc Bψψ p : ℝ) : Prop where
  det_ne : Bcc * Bψψ - Bcψ * Bψc ≠ 0
  eq422 : Bmat Bcc Bcψ Bψc Bψψ * M' 0 0 = Pmat p

/-- The double point s*(θ) = −1 + √(1−μ₀(θ)): zero at θ = 0, continuous there, negative for
θ ≠ 0 (μ₀(θ) = θ²‖ω‖²/vol + O(θ⁴) by Kato–Rellich off the simple eigenvalue 0). -/
structure DoublePoint (sStar : ℝ → ℝ) : Prop where
  zero : sStar 0 = 0
  cont : ContinuousAt sStar 0
  neg : ∀ θ, θ ≠ 0 → sStar θ < 0

end Ledger

end FriedCrossing
