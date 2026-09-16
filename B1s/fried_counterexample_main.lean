/-
THE STATEMENT FILE — Fried's identity fails at the crossing metric, from the input ledger.

This file states ONE theorem, `fried_counterexample_of_inputs`, whose hypothesis list is the
complete ledger of analytic facts the counterexample consumes. Its proof only composes the leg
files (`fried_crossing_9_03` → `fried_crossing_rate_9_07` → `fried_crossing_firstvariation_9_08`
→ `fried_crossing_purezeros_9_08` → `fried_cluster_matrices_9_10`). Nothing analytic is proved
here or anywhere in the suite; every hypothesis below is a fact about finite-dimensional data that
a human checks against the cited source. `#print axioms` at the bottom certifies that nothing else
was assumed.

DESIGN (9/08, per Ben): ONE BINDER PER MATHEMATICAL FACT. Where a fact has several technical
components they are bundled as the named fields of a `structure` (§1 here, or `Ledger` in the
9/10 leg file), so that the theorem's hypothesis list and the README ledger table are in
one-to-one correspondence (`scripts/ledger_check.py` enforces one name per row). Each binder
carries a one-line comment: what it says, where it comes from, and its status — [V] verbatim in
the cited paper, [D] derived in the vault memos from cited facts, [U] not literally in any paper we
hold (the open items), [def] a definition or case split rather than a fact.

9/10 REVISION — THE CLUSTER MATRICES ARE THE PRIMITIVES. The objects are now the two cluster
matrices M (2×2, degree 1) and A (4×4, degree 2) on the ranges of the Riesz projectors for the
disc D ∋ 0, as functions of (θ,τ). Everything else is DEFINED from them in
`fried_cluster_matrices_9_10.lean`: ∂_τM (`Derived.Mτ`), N = (M − s*·1)/τ (`Hadamard.Ndiv`) and
its trace/determinant derivatives (`Derived.aτ`, `Derived.bτ`), the pure-quadratic coefficients
e₁ = c₁(A) − tr M, e₂ = c₂(A) − det M − (tr M)e₁ (`Derived.E₁f`, `E₂f`), and their partials
(`Regularity.pτ`, `pθ`). Consequences for the ledger, all machine-checked in that file:
  • the four regularity bundles (ClusterC1, TraceDetC1, PureSumC2, PureProdC3) collapse to ONE
    hypothesis `ClusterC3` — joint C³ of the matrix entries — the whole of input (B);
  • mirror (A) and pinning (D) are spectra of A: {s*,s*,s*,−s*} at τ = 0, {0,0,0,twin} at θ = 0;
  • the locked branches enter as `hlocked` (DGRS Lemma 7.1 shape);
  • the former `hexactZero` and `hgeneric` are DERIVED from exactness through the dictionary
    `hriesz` (c_k = algebraic multiplicity of 0 in the degree-k cluster matrix);
  • (9/11) the pure-zero branch z is DEFINED as the root of Q nearest 0 (`Branch.zBranch`), which
    is the branch through 0 at a crossing because 0 is a simple root there — the former `hzQ` and
    `hbranch` are gone;
  • (9/11) the ζ-side is the two facts it really is: `hfactor` = Chaubet–Dang (6.5) at λ = 0
    (`ZetaFactorization`: ζ₀ = F·z/s off the crossing, F continuous, ζ₀(σ) = F(σ)) and
    `hfried_off` = ζ₀ = τ_R off the crossing (DGRS Thm 2 + Fried at g_hyp). The conclusion is
    stated for ζ₀(σ) = ζ(0; g_σ) itself;
  • (9/11) C₀¹ and C₀² are DEFINED as the generalized 0-eigenspaces of the cluster matrices
    (`Derived.resZero₁`, `resZero₂`); their dimensions are the algebraic multiplicities by Mathlib's
    `LinearMap.finrank_maxGenEigenspace_eq`, so the dictionary row `hriesz` is gone. C₀³ stays an
    abstract space V₃: the proof uses only its dimension (rank–nullity), and no degree-3 matrix is
    in the ledger.
22 binders → 18 (9/10) → 16 → 15 (9/11); [U] 4 → 1.

9/14 — `hsemisimple` REPLACED BY ITS INPUT. The semisimple double point M(θ,0) = s*·1 is now
DERIVED (`Derived.semisimple_of_states`, wrapping `Saturation` §6 of the rate file through
`Matrix.toLin'`) from `hstates`: two linearly independent resonant states at s*(θ) in the degree-1
cluster at g_hyp (d₀f and I·d₀f, rederivation A2). The cluster's rank 2 is the type Fin 2 (DGRS
Prop 7.7 + bounded-twist rank constancy). Every remaining binder is a cited fact or a definition.

9/11 EVENING — INPUT (B) DERIVED. `fried_counterexample_of_resolvent_inputs` (§3 below) is the same
theorem with the cluster matrices DEFINED from the analysis: two resolvent families on two Banach
scales (`Scale.ResolventFamily`: the resolvent of the twisted deformed generator P(θ,τ) − λ, bounded
locally uniformly on every level and inverting the generator modulo the inclusions — CDDP Lemma 4.3;
the generator smooth in (θ,τ,λ)), complex structures J, and nondegenerate frames (φ_j, ℓ_l) at
(0,0) (CP20 §6.2). `resolvent_scale_9_11` iterates the resolvent identity (4.12)–(4.13) to C³ with
loss; `cluster_from_resolvent_9_11` integrates over a fixed contour and inverts the frame Gram
matrix. `hclusterC3` is then a THEOREM (`ClusterFrame.clusterC3_of_resolvent`) and the ledger has
no uncited row. M and A are the real parts of the frame matrices A⁻¹B; that their imaginary parts
vanish (conjugation symmetry of the cluster) is what makes them THE cluster matrices — an
interpretive fact, not consumed by the proof.

The mathematics: on a closed hyperbolic 3-manifold Z with b₁ = 1, characters χ_θ, conformal family
g_τ = e^{−2τb}g_hyp; the non-closed degree-1 resonance (the "twin") starts at s*(θ) < 0 and crosses
0 at τ = σ(θ); there ζ is regular at 0 but ζ(0; g_σ) = τ_R · (pole rate)/(zero rate) ≠ τ_R.

Objects (all finite-dimensional or real-valued):
  M          the 2×2 degree-1 cluster matrix at (θ,τ) (range of the rank-2 Riesz projector);
  A          the 4×4 degree-2 cluster matrix at (θ,τ) (range of the rank-4 Riesz projector);
  sStar      θ ↦ s*(θ), the double point at g_hyp;
  B, p       the pairing matrix on Res¹₀ in the basis (c, ψ) and the (4.22) pairing of the
             non-closed state (Bcc Bcψ Bψc Bψψ, p);
  ζ₀, F      τ ↦ ζ(0; g_τ) and the regular factor F(0,τ) of CD (6.5); z = the pure-zero branch is
             DEFINED;
  c, V₃      the reduced resonant dimensions c_k = dim C₀^k and the abstract degree-3 space; C₀¹,
             C₀² are DEFINED (`resZero₁ M θ σ`, `resZero₂ A θ σ`);
  τR         τ_R(χ_θ) = ζ_{χ_θ}(0; g_hyp).
-/
import B1s.cluster_from_resolvent_9_11

set_option linter.style.header false

namespace FriedCrossing

open Filter Topology TwinRate FirstVariation Hadamard PureZeros Capstone OrderCount TorsionCore
  Derived Regularity Ledger Branch

/-! ## §1 The hypothesis bundles `FirstVariation422`, `DoublePoint` now live in
`B1s/fried_statement_defs_9_14.lean` with every other statement definition (9/14). -/

/-! ## §2 The statement -/

-- The conclusion's hypotheses are NAMED (`∀ (hzQ : …), …`) so that the ledger table in the README
-- can refer to them (`scripts/ledger_check.py` compares the two); the proof consumes them by
-- unification, so the unused-variable linter is switched off for this one declaration.
set_option linter.unusedVariables false in
/-- **Fried's identity fails at the crossing metric** — THE LEDGER. One binder per fact. -/
theorem fried_counterexample_of_inputs
    {V₃ : Type*} [AddCommGroup V₃] [Module ℝ V₃]
    (M : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (A : ℝ → ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (sStar : ℝ → ℝ) (Bcc Bcψ Bψc Bψψ p : ℝ)
    -- [D] hstates: two linearly independent resonant states at s*(θ) in the degree-1 cluster at
    --     g_hyp — d₀f (from the degree-0 state f) and I·d₀f (I = rotation on E_u ⊕ E_s commutes
    --     with the flow, CDDP (3.7)); independence by the Liouville argument on S² (rederivation
    --     A2). The cluster's rank 2 is the TYPE Fin 2 [DGRS Prop 7.7 m₁(0) = 2b₁ at θ = 0 +
    --     bounded-twist rank constancy]. Together they GIVE M(θ,0) = s*·1 (`Derived.semisimple_of_states`,
    --     the former `hsemisimple`).
    (hstates : ∀ θ, ∃ v₁ v₂ : Fin 2 → ℝ, LinearIndependent ℝ ![v₁, v₂] ∧
      Matrix.mulVec (M θ 0) v₁ = sStar θ • v₁ ∧ Matrix.mulVec (M θ 0) v₂ = sStar θ • v₂)
    -- [U] INPUT (B), the whole of it: the entries of both cluster matrices are jointly C³ in
    --     (θ,τ). CDDP Lemma 4.3 gives continuity of the resolvent; the derivatives are resolvent
    --     perturbation on a flow-independent anisotropic space (target: Bonthonneau 1806.08125);
    --     the Cauchy-estimate alternative is vault input_b_cauchy_route_9_09 (PROPOSED).
    (hclusterC3 : ClusterC3 M A)
    -- [V] CDDP (4.22) + (4.38) + Lemmas 2.2/2.10, for ∂_τM(0,0) = `Derived.Mτ M 0 0`.
    (h422 : FirstVariation422 (Mτ M) Bcc Bcψ Bψc Bψψ p)
    -- [V] r₀ := Bcc·p/det B ≠ 0 is CDDP's non-degeneracy (1.3) for b in the open dense set O
    --     (Thm 1(2)); the sign is the orientation of τ.
    (hr₀ : 0 < Bcc * p / (Bcc * Bψψ - Bcψ * Bψc))
    -- [V] s*(θ) = −1 + √(1−μ₀(θ)): DGRS (7.6) as a meromorphic identity + BuOl Cor 5.1 (scalar
    --     Selberg zeros, cited via DGRS) + DFG Thm 2 cross-check; μ₀ by Kato–Rellich.
    (hdouble : DoublePoint sStar)
    -- [V]+[D] mirror (input A): the degree-2 cluster at g_hyp has spectrum {s*, s*, s*, −s*} —
    --     the locked pair at s* (DGRS Lemma 7.1) and the pure pair at ±s*: DGRS (7.6) k = 2
    --     factors Z_{S,σ₀}(λ) and Z_{S,σ₀}(λ+2) (dgrs 1876–1884) + BuOl zeros [V]; the −s* state
    --     identified as f'·ω_s (rederivation A2, rate-ratio memo §2.1) [D].
    (hmirror : ∀ θ z, (A θ 0).charpoly.eval z = (z - sStar θ) ^ 3 * (z + sStar θ))
    -- [V] pinning (input D) at ρ_triv: det M(0,τ) = 0 (the harmonic 1-form, b₁ = 1) and
    --     spec A(0,τ) = {0, 0, 0, twin} — 0 with multiplicity b₁ + 2 = 3 (CDDP Cor 4.1 via
    --     Thm 1(2)) and the lifted twin d₀u_nc (DGRS Lemma 7.1), whose value is tr M(0,τ).
    (hpinning : Pinned M A)
    -- [V] locked branches: every degree-1 cluster eigenvalue is a degree-2 cluster eigenvalue —
    --     d₀ commutes with L_X (DGRS Lemma 7.1) lifts the twin; ∧dα lifts the closed branch
    --     (f·dα = d₀²f/s_cl).
    (hlocked : ∀ θ τ z, (M θ τ).charpoly.eval z = 0 → (A θ τ).charpoly.eval z = 0) :
    let a : ℝ → ℝ → ℝ := fun θ τ => (Ndiv M (Mτ M) sStar θ τ).trace
    let b : ℝ → ℝ → ℝ := fun θ τ => (Ndiv M (Mτ M) sStar θ τ).det
    let a' : ℝ → ℝ → ℝ := aτ M
    let b' : ℝ → ℝ → ℝ := bτ M sStar
    let e₁ : ℝ → ℝ → ℝ := E₁f M A
    let e₂ : ℝ → ℝ → ℝ := E₂f M A
    let e₂τ : ℝ → ℝ → ℝ := pτ e₂
    -- the pure-zero branch: the root of z² − e₁z + e₂ nearest 0 (through 0 at a crossing, where 0
    -- is a simple root; `Branch.zBranch_at_simple_zero`). DEFINED — no binder.
    let z : ℝ → ℝ → ℝ := fun θ => zBranch (e₁ θ) (e₂ θ)
    let r₀ : ℝ := Bcc * p / (Bcc * Bψψ - Bcψ * Bψc)
    ∃ K₁ : ℝ, 0 < K₁ ∧ ∃ θ₀ δ : ℝ, 0 < θ₀ ∧ 0 < δ ∧ ∀ θ, θ ≠ 0 → |θ| < θ₀ →
      ∀ (ζ₀ F : ℝ → ℝ) (c : Fin 5 → ℕ) (τR : ℝ),
        -- [V] τ_R(χ_θ) ≠ 0: Reidemeister torsion of an acyclic character (Fried 1986 at g_hyp).
        ∀ (hτR : τR ≠ 0),
        -- [V] Chaubet–Dang (6.5) at λ = 0 along the family: ζ₀(τ) = ζ(0; g_τ) = F(τ)·z(τ)/s_nc(τ)
        --     off the crossing (`off`), the regular factor F continuous at the crossing (`cont`,
        --     input (B)), and ζ₀(σ) = F(σ) at the crossing where the cluster factor is λ/λ
        --     (`at_crossing`). z is the DEFINED pure-zero branch.
        ∀ (hfactor : ZetaFactorization ζ₀ F (twin sStar a b θ) (z θ) δ),
        -- [V] off the crossing Fried holds: ζ(0; g_τ) = τ_R — DGRS Thm 2 local constancy of
        --     ζ(0) in the vector field + Fried at g_hyp.
        ∀ (hfried_off : ∀ τ, |τ| < δ → twin sStar a b θ τ ≠ 0 → ζ₀ τ = τR),
        -- [V] the reduced resonant complex C₀¹ → C₀² → C₀³ at each crossing inside |τ| < δ is
        --     exact (Dang–Rivière Thm 2.1 / DGRS (7.1), rederivation A6), with C₀¹, C₀² the
        --     generalized 0-eigenspaces of the cluster matrices and C₀³ the abstract V₃.
        ∀ (hexact : ∀ τ₀, |τ₀| < δ → twin sStar a b θ τ₀ = 0 →
          ∃ (f : resZero₁ M θ τ₀ →ₗ[ℝ] resZero₂ A θ τ₀) (g : resZero₂ A θ τ₀ →ₗ[ℝ] V₃),
            Function.Injective f ∧ LinearMap.range f = LinearMap.ker g ∧ Function.Surjective g),
        -- [V] c₀ = c₄ = 0 for acyclic unitary ρ: DGRS Lemma 7.4 (+ ⋆).
        ∀ (hacyc : c 0 = 0 ∧ c 4 = 0),
        -- [V] c₃ = c₁: ⋆-duality, DGRS Lemma 7.2.
        ∀ (hdual : c 3 = c 1),
        -- [def] c_k = dim C₀^k, k = 1, 2, 3, at each crossing inside |τ| < δ (dimensions of the
        --     generalized 0-eigenspaces = algebraic multiplicities of 0, by Mathlib).
        ∀ (hdims : ∀ τ₀, |τ₀| < δ → twin sStar a b θ τ₀ = 0 →
          c 1 = Module.finrank ℝ (resZero₁ M θ τ₀) ∧ c 2 = Module.finrank ℝ (resZero₂ A θ τ₀) ∧
          c 3 = Module.finrank ℝ V₃),
        -- ══ CONCLUSION ═══════════════════════════════════════════════════════════════════════
        ∃ σ, 0 < σ ∧ σ ≤ 2 * |sStar θ| / r₀ ∧ σ < δ ∧ twin sStar a b θ σ = 0 ∧
          (∀ τ, |τ| < δ → twin sStar a b θ τ = 0 → τ = σ) ∧          -- unique crossing
          zetaOrder c = 0 ∧                                            -- ζ regular at 0
          HasDerivAt (z θ) (e₂τ θ σ / e₁ θ σ) σ ∧ 2 * r₀ < |e₂τ θ σ / e₁ θ σ| ∧   -- zero steeper
          |e₁ θ σ| ≤ K₁ * |θ| * σ ∧                                    -- than the pole
          ∃ α ratio : ℝ, α ≠ 0 ∧ dtwin (a θ σ) (b θ σ) (a' θ σ) (b' θ σ) σ ≠ 0 ∧
            Tendsto (fun τ => twin sStar a b θ τ / z θ τ) (𝓝[≠] σ) (𝓝 ratio) ∧
            ratio = dtwin (a θ σ) (b θ σ) (a' θ σ) (b' θ σ) σ / α ∧ ratio ≠ 1 ∧
            ζ₀ σ = τR * ratio ∧ ζ₀ σ ≠ τR ∧                            -- ζ(0;g_σ) ≠ τ_R
            refinedTorsion 1 (dtwin (a θ σ) (b θ σ) (a' θ σ) (b' θ σ) σ /
              (α - dtwin (a θ σ) (b θ σ) (a' θ σ) (b' θ σ) σ)) =
              -(α / dtwin (a θ σ) (b θ σ) (a' θ σ) (b' θ σ) σ) := by   -- Lemma A
  intro a b a' b' e₁ e₂ e₂τ z r₀
  exact fried_fails_at_crossing_of_matrix_inputs (V₃ := V₃)
    M A sStar Bcc Bcψ Bψc Bψψ p (semisimple_of_states M sStar hstates) hclusterC3 h422.det_ne
    h422.eq422 hr₀
    hdouble.zero hdouble.cont hdouble.neg hmirror hpinning hlocked

/-! ## §3 The statement with input (B) derived from the resolvent -/

open Scale ClusterFrame in
set_option linter.unusedVariables false in
/-- **Fried's identity fails at the crossing metric — no uncited input.** The cluster matrices are
M := `Mreal F₁ J₁ D₁` (2×2, degree 1) and A := `Mreal F₂ J₂ D₂` (4×4, degree 2): real parts of the
frame matrices A(p)⁻¹B(p) built from contour integrals of matrix elements of the resolvent families.
Input (B) is replaced by the fields of `F₁`, `F₂` (CDDP Lemma 4.3 + generator smoothness, [V]) and
the frame nondegeneracy `hdet₁`, `hdet₂` ([def]: dual frame at (0,0), CP20 §6.2). Every other binder is
as in `fried_counterexample_of_inputs`. -/
theorem fried_counterexample_of_resolvent_inputs
    {V₃ : Type*} [AddCommGroup V₃] [Module ℝ V₃]
    {S₁ S₂ : BanachScale.{0}}
    (F₁ : ResolventFamily S₁ Param) (J₁ : ComplexStructure S₁) (D₁ : FrameData S₁ 2)
    (F₂ : ResolventFamily S₂ Param) (J₂ : ComplexStructure S₂) (D₂ : FrameData S₂ 4)
    (sStar : ℝ → ℝ) (Bcc Bcψ Bψc Bψψ p : ℝ)
    -- [def] the frames are nondegenerate: det A(p) ≠ 0 (dual frame at (0,0), retracted parameters).
    (hdet₁ : ∀ q, (Amat F₁ J₁ D₁ q).det ≠ 0)
    (hdet₂ : ∀ q, (Amat F₂ J₂ D₂ q).det ≠ 0)
    -- [D] two independent states d₀f, I·d₀f at s*(θ) in the degree-1 cluster at g_hyp
    --     (rederivation A2); rank 2 = the type.
    (hstates : ∀ θ, ∃ v₁ v₂ : Fin 2 → ℝ, LinearIndependent ℝ ![v₁, v₂] ∧
      Matrix.mulVec (Mreal F₁ J₁ D₁ θ 0) v₁ = sStar θ • v₁ ∧
      Matrix.mulVec (Mreal F₁ J₁ D₁ θ 0) v₂ = sStar θ • v₂)
    (h422 : FirstVariation422 (Mτ (Mreal F₁ J₁ D₁)) Bcc Bcψ Bψc Bψψ p)
    (hr₀ : 0 < Bcc * p / (Bcc * Bψψ - Bcψ * Bψc))
    (hdouble : DoublePoint sStar)
    (hmirror : ∀ θ z, (Mreal F₂ J₂ D₂ θ 0).charpoly.eval z = (z - sStar θ) ^ 3 * (z + sStar θ))
    (hpinning : Pinned (Mreal F₁ J₁ D₁) (Mreal F₂ J₂ D₂))
    (hlocked : ∀ θ τ z, (Mreal F₁ J₁ D₁ θ τ).charpoly.eval z = 0 →
      (Mreal F₂ J₂ D₂ θ τ).charpoly.eval z = 0) :
    let M := Mreal F₁ J₁ D₁
    let A := Mreal F₂ J₂ D₂
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
        ∀ (hτR : τR ≠ 0),
        ∀ (hfactor : ZetaFactorization ζ₀ F (twin sStar a b θ) (z θ) δ),
        ∀ (hfried_off : ∀ τ, |τ| < δ → twin sStar a b θ τ ≠ 0 → ζ₀ τ = τR),
        ∀ (hexact : ∀ τ₀, |τ₀| < δ → twin sStar a b θ τ₀ = 0 →
          ∃ (f : resZero₁ M θ τ₀ →ₗ[ℝ] resZero₂ A θ τ₀) (g : resZero₂ A θ τ₀ →ₗ[ℝ] V₃),
            Function.Injective f ∧ LinearMap.range f = LinearMap.ker g ∧ Function.Surjective g),
        ∀ (hacyc : c 0 = 0 ∧ c 4 = 0),
        ∀ (hdual : c 3 = c 1),
        ∀ (hdims : ∀ τ₀, |τ₀| < δ → twin sStar a b θ τ₀ = 0 →
          c 1 = Module.finrank ℝ (resZero₁ M θ τ₀) ∧ c 2 = Module.finrank ℝ (resZero₂ A θ τ₀) ∧
          c 3 = Module.finrank ℝ V₃),
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
              -(α / dtwin (a θ σ) (b θ σ) (a' θ σ) (b' θ σ) σ) :=
  fried_counterexample_of_inputs (V₃ := V₃) (Mreal F₁ J₁ D₁) (Mreal F₂ J₂ D₂) sStar
    Bcc Bcψ Bψc Bψψ p hstates (clusterC3_of_resolvent F₁ J₁ D₁ F₂ J₂ D₂ hdet₁ hdet₂)
    h422 hr₀ hdouble hmirror hpinning hlocked

end FriedCrossing

/-! The certificates: the build log prints the axioms the statements depend on. Expected:
`[propext, Classical.choice, Quot.sound]` — Lean's built-ins, nothing of ours. -/
#print axioms FriedCrossing.fried_counterexample_of_inputs
#print axioms FriedCrossing.fried_counterexample_of_resolvent_inputs
