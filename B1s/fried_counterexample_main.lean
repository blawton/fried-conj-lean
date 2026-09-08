/-
THE STATEMENT FILE — Fried's identity fails at the crossing metric, from the input ledger.

This file states ONE theorem, `fried_counterexample_of_inputs`, whose hypothesis list is the
complete ledger of analytic facts the counterexample consumes. Its proof only composes the three
leg files (`fried_crossing_rate_9_07`, `fried_crossing_firstvariation_9_08`,
`fried_crossing_purezeros_9_08`) on top of `fried_crossing_9_03`. Nothing analytic is proved here
or anywhere in the suite; every hypothesis below is a fact about finite-dimensional data that a
human checks against the cited source. `#print axioms` at the bottom certifies that nothing else
was assumed.

DESIGN (9/08, per Ben): ONE BINDER PER MATHEMATICAL FACT. Where a fact has several technical
components (a derivative, its continuity, a bound) they are bundled as the named fields of a
`structure` declared in §1, so that the theorem's hypothesis list and the README ledger table are
in one-to-one correspondence (`scripts/ledger_check.py` enforces one name per row). Each binder
carries a one-line comment: what it says, where it comes from, and its status — [V] verbatim in
the cited paper, [D] derived in the vault memos from cited facts, [U] not literally in any paper we
hold (the open items), [def] a definition or case split rather than a fact.

The mathematics: on a closed hyperbolic 3-manifold Z with b₁ = 1, characters χ_θ, conformal family
g_τ = e^{−2τb}g_hyp; the non-closed degree-1 resonance (the "twin") starts at s*(θ) < 0 and crosses
0 at τ = σ(θ); there ζ is regular at 0 but ζ(0; g_σ) = τ_R · (pole rate)/(zero rate) ≠ τ_R.

Objects (all finite-dimensional or real-valued):
  M, M'      the 2×2 degree-1 cluster matrix at (θ,τ) on the range of the rank-2 Riesz projector,
             and its τ-derivative (entrywise);
  sStar      θ ↦ s*(θ), the double point at g_hyp;
  B, p       the pairing matrix on Res¹₀ in the basis (c, ψ) and the (4.22) pairing of the
             non-closed state (Bcc Bcψ Bψc Bψψ, p);
  a', b'     τ-derivatives of a = tr N, b = det N, where M − s*·1 = τ·N;
  e₁, e₂     sum and product of the two PURE degree-2 branches (char quartic of the rank-4
             cluster ÷ the two locked branches), with derivative data e₁τ e₁θτ e₂τ e₂ττ e₂θττ;
  z, R       the pure-zero branch through 0 and the regular factor of ζ at 0 (CD (6.5));
  c, V₁ V₂ V₃ the reduced resonant dimensions and spaces of the zero cluster at the crossing;
  τR         τ_R(χ_θ) = ζ_{χ_θ}(0; g_hyp).
-/
import B1s.fried_crossing_purezeros_9_08

set_option linter.style.header false

namespace FriedCrossing

open Filter Topology TwinRate FirstVariation Hadamard PureZeros Capstone OrderCount TorsionCore

/-! ## §1 The hypothesis bundles — one structure per multi-component fact -/
namespace Ledger

/-- The degree-1 cluster matrix is C¹ in τ (entrywise) with ∂_τM jointly continuous at (0,0).
Rank-2 half of input (B). -/
structure ClusterC1 (M M' : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ) : Prop where
  deriv : ∀ θ τ i j, HasDerivAt (fun t => M θ t i j) (M' θ τ i j) τ
  cont : ∀ i j, ContinuousAt (fun q : ℝ × ℝ => M' q.1 q.2 i j) (0, 0)

/-- CDDP (4.22): in the basis (c, ψ) of Res¹₀ with pairing B (invertible, Lemmas 2.2 + 2.10), the
first-variation matrix ∂_τM(0,0) solves B·∂_τM(0,0) = P = !![0,0;0,p] — the c-row and c-column
vanish because dc = 0, and p is the (4.22) pairing of the non-closed state (with (4.38)). -/
structure FirstVariation422 (M' : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (Bcc Bcψ Bψc Bψψ p : ℝ) : Prop where
  det_ne : Bcc * Bψψ - Bcψ * Bψc ≠ 0
  eq422 : Bmat Bcc Bcψ Bψc Bψψ * M' 0 0 = Pmat p

/-- a = tr N and b = det N (M − s*·1 = τ·N) are C¹ in τ with jointly continuous derivatives:
one derivative beyond `Hadamard` §2 (M C² in τ suffices). Rank-2 half of input (B). -/
structure TraceDetC1 (M M' : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (sStar : ℝ → ℝ)
    (a' b' : ℝ → ℝ → ℝ) : Prop where
  deriv_a : ∀ θ τ, HasDerivAt (fun τ => (Ndiv M M' sStar θ τ).trace) (a' θ τ) τ
  deriv_b : ∀ θ τ, HasDerivAt (fun τ => (Ndiv M M' sStar θ τ).det) (b' θ τ) τ
  cont_a' : ContinuousAt (Function.uncurry a') (0, 0)
  cont_b' : ContinuousAt (Function.uncurry b') (0, 0)

/-- The double point s*(θ) = −1 + √(1−μ₀(θ)): zero at θ = 0, continuous there, negative for
θ ≠ 0 (μ₀(θ) = θ²‖ω‖²/vol + O(θ⁴) by Kato–Rellich off the simple eigenvalue 0). -/
structure DoublePoint (sStar : ℝ → ℝ) : Prop where
  zero : sStar 0 = 0
  cont : ContinuousAt sStar 0
  neg : ∀ θ, θ ≠ 0 → sStar θ < 0

/-- e₁ (sum of the pure degree-2 branches) has a bounded mixed partial ∂_θ∂_τe₁ on the
(θ,τ)-square of radius ε about (0,0): joint C². Rank-4 half of input (B) — THE load-bearing
uncited item; C² of e₁ is all the counterexample needs. -/
structure PureSumC2 (e₁ e₁τ e₁θτ : ℝ → ℝ → ℝ) (K₁ ε : ℝ) : Prop where
  K_pos : 0 < K₁
  ε_pos : 0 < ε
  deriv_τ : ∀ θ τ, HasDerivAt (e₁ θ) (e₁τ θ τ) τ
  deriv_θτ : ∀ θ τ, HasDerivAt (fun θ => e₁τ θ τ) (e₁θτ θ τ) θ
  bound : ∀ θ τ, |θ| < ε → |τ| < ε → |e₁θτ θ τ| ≤ K₁

/-- e₂ (product of the pure degree-2 branches) has ∂²_τe₂ with a bounded θ-derivative on the same
square. Rank-4 half of input (B). -/
structure PureProdC3 (e₂ e₂τ e₂ττ e₂θττ : ℝ → ℝ → ℝ) (K₂ ε : ℝ) : Prop where
  K_pos : 0 < K₂
  deriv_τ : ∀ θ τ, HasDerivAt (e₂ θ) (e₂τ θ τ) τ
  deriv_ττ : ∀ θ τ, HasDerivAt (e₂τ θ) (e₂ττ θ τ) τ
  deriv_θττ : ∀ θ τ, HasDerivAt (fun θ => e₂ττ θ τ) (e₂θττ θ τ) θ
  bound : ∀ θ τ, |θ| < ε → |τ| < ε → |e₂θττ θ τ| ≤ K₂

/-- Pinning at ρ_triv (CDDP Cor 4.1 via Thm 1(2)): for 0 < |τ| < ε₀ the degree-2 multiplicity of
0 is b₁ + 2, so the pole leaves 0 ALONE and both pure zeros stay at 0. -/
structure Pinning (e₁ e₂ : ℝ → ℝ → ℝ) : Prop where
  sum : ∀ τ, e₁ 0 τ = 0
  prod : ∀ τ, e₂ 0 τ = 0

end Ledger

open Ledger

/-! ## §2 The statement -/

-- The conclusion's hypotheses are NAMED (`∀ (hzQ : …), …`) so that the ledger table in the README
-- can refer to them (`scripts/ledger_check.py` compares the two); the proof consumes them by
-- unification, so the unused-variable linter is switched off for this one declaration.
set_option linter.unusedVariables false in
/-- **Fried's identity fails at the crossing metric** — THE LEDGER. One binder per fact. -/
theorem fried_counterexample_of_inputs
    {K : Type*} [Field K] {V₁ V₂ V₃ : Type*}
    [AddCommGroup V₁] [Module K V₁] [FiniteDimensional K V₁]
    [AddCommGroup V₂] [Module K V₂] [FiniteDimensional K V₂]
    [AddCommGroup V₃] [Module K V₃]
    (M M' : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (sStar : ℝ → ℝ)
    (Bcc Bcψ Bψc Bψψ p : ℝ) (a' b' : ℝ → ℝ → ℝ)
    (e₁ e₂ e₁τ e₁θτ e₂τ e₂ττ e₂θττ : ℝ → ℝ → ℝ) {K₁ K₂ ε : ℝ}
    -- [D] hdouble: the degree-1 cluster at g_hyp is the SEMISIMPLE double point, M(θ,0) = s*·1.
    --     `Saturation` (rate file §6): rank 2 [DGRS Prop 7.7 at θ = 0 + bounded-twist rank
    --     constancy] + two independent states d₀f, I·d₀f at s* [rederivation A2].
    (hsemisimple : ∀ θ, M θ 0 = sStar θ • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    -- [U] input (B), rank-2 half: CDDP Lemma 4.3 gives continuity of the resolvent; one
    --     derivative more is standard resolvent perturbation (target: Bonthonneau 1806.08125).
    (hclusterC1 : ClusterC1 M M')
    -- [V] CDDP (4.22) + (4.38) + Lemmas 2.2/2.10.
    (h422 : FirstVariation422 M' Bcc Bcψ Bψc Bψψ p)
    -- [V] r₀ := Bcc·p/det B ≠ 0 is CDDP's non-degeneracy (1.3) for b in the open dense set O
    --     (Thm 1(2)); the sign is the orientation of τ.
    (hr₀ : 0 < Bcc * p / (Bcc * Bψψ - Bcψ * Bψc))
    -- [U] input (B), rank-2 half, one derivative more (same source as hclusterC1).
    (htraceDetC1 : TraceDetC1 M M' sStar a' b')
    -- [V] s*(θ) = −1 + √(1−μ₀(θ)): DGRS (7.6) as a meromorphic identity + BuOl Cor 5.1 (scalar
    --     Selberg zeros, cited via DGRS) + DFG Thm 2 cross-check; μ₀ by Kato–Rellich.
    (hdouble : DoublePoint sStar)
    -- [U] input (B), rank-4 half — THE load-bearing uncited item.
    (hpureSumC2 : PureSumC2 e₁ e₁τ e₁θτ K₁ ε)
    -- [U] input (B), rank-4 half.
    (hpureProdC3 : PureProdC3 e₂ e₂τ e₂ττ e₂θττ K₂ ε)
    -- [V] mirror (input A): the two pure degree-2 zeros at g_hyp sit at ±s*, so e₁(θ,0) = 0 —
    --     DGRS (7.6) k = 2 factors Z_{S,σ₀}(λ) and Z_{S,σ₀}(λ+2) (dgrs 1876–1884) + BuOl zeros.
    (hmirror_sum : ∀ θ, e₁ θ 0 = 0)
    -- [D] mirror (input A): their product e₂(θ,0) = −s*²; the −s* state identified as f'·ω_s
    --     (rederivation A2, rate-ratio memo §2.1).
    (hmirror_prod : ∀ θ, e₂ θ 0 = -(sStar θ) ^ 2)
    -- [V] pinning (input D): CDDP Cor 4.1 via Thm 1(2).
    (hpinning : Pinning e₁ e₂) :
    let a : ℝ → ℝ → ℝ := fun θ τ => (Ndiv M M' sStar θ τ).trace
    let b : ℝ → ℝ → ℝ := fun θ τ => (Ndiv M M' sStar θ τ).det
    let r₀ : ℝ := Bcc * p / (Bcc * Bψψ - Bcψ * Bψc)
    ∃ θ₀ δ : ℝ, 0 < θ₀ ∧ 0 < δ ∧ ∀ θ, θ ≠ 0 → |θ| < θ₀ →
      ∀ (z R : ℝ → ℝ) (c : Fin 5 → ℕ) (τR : ℝ),
        -- [V] τ_R(χ_θ) ≠ 0: Reidemeister torsion of an acyclic character (Fried 1986 at g_hyp).
        ∀ (hτR : τR ≠ 0),
        -- [D] z is a root of the pure quadratic z² − e₁z + e₂: quartic division
        --     (`PureZeros.quartic_roots`), given the locked branches s_cl (f·dα) and s_nc (d₀u_nc)
        --     are roots (DGRS Lemma 7.1: d₀ commutes with L_X).
        ∀ (hzQ : ∀ τ, z τ ^ 2 - e₁ θ τ * z τ + e₂ θ τ = 0),
        -- [def] z is the continuous pure-zero branch through 0 at each crossing inside |τ| < δ.
        ∀ (hbranch : ∀ τ₀, |τ₀| < δ → twin sStar a b θ τ₀ = 0 → ContinuousAt z τ₀ ∧ z τ₀ = 0),
        -- [V] exactness (input E, Dang–Rivière Thm 2.1 / DGRS (7.1)): at a crossing a pure
        --     degree-2 zero sits at 0, i.e. e₂(θ,σ) = 0.
        ∀ (hexactZero : ∀ τ₀, |τ₀| < δ → twin sStar a b θ τ₀ = 0 → e₂ θ τ₀ = 0),
        -- [def] generic case e₁(θ,σ) ≠ 0 (the degenerate alternative c₂ = 3, ord₀ζ = +1, is not in
        --     the Lean and also fails Fried).
        ∀ (hgeneric : ∀ τ₀, |τ₀| < δ → twin sStar a b θ τ₀ = 0 → e₁ θ τ₀ ≠ 0),
        -- [V] the regular factor F(0,·) of CD (6.5) is continuous at the crossing (input (B)).
        ∀ (hregular : ∀ τ₀, twin sStar a b θ τ₀ = 0 → ContinuousAt R τ₀),
        -- [V] off the crossing, Fried holds: ζ(0; g_τ) = R·z/s_nc = τ_R — DGRS Thm 2 local
        --     constancy + Fried at g_hyp.
        ∀ (hfried_off : ∀ τ, |τ| < δ → twin sStar a b θ τ ≠ 0 →
          R τ * z τ / twin sStar a b θ τ = τR),
        -- [V] the reduced resonant complex C₀¹ → C₀² → C₀³ at the crossing is exact
        --     (Dang–Rivière Thm 2.1 / DGRS (7.1), rederivation A6).
        ∀ (hexact : ∃ (f : V₁ →ₗ[K] V₂) (g : V₂ →ₗ[K] V₃), Function.Injective f ∧
          LinearMap.range f = LinearMap.ker g ∧ Function.Surjective g),
        -- [V] c₀ = c₄ = 0 for acyclic unitary ρ: DGRS Lemma 7.4 (+ ⋆).
        ∀ (hacyc : c 0 = 0 ∧ c 4 = 0),
        -- [V] c₃ = c₁: ⋆-duality, DGRS Lemma 7.2.
        ∀ (hdual : c 3 = c 1),
        -- [def] c_k = dim C₀^k, k = 1, 2, 3.
        ∀ (hdims : c 1 = Module.finrank K V₁ ∧ c 2 = Module.finrank K V₂ ∧
          c 3 = Module.finrank K V₃),
        -- ══ CONCLUSION ═══════════════════════════════════════════════════════════════════════
        ∃ σ, 0 < σ ∧ σ ≤ 2 * |sStar θ| / r₀ ∧ σ < δ ∧ twin sStar a b θ σ = 0 ∧
          (∀ τ, |τ| < δ → twin sStar a b θ τ = 0 → τ = σ) ∧          -- unique crossing
          zetaOrder c = 0 ∧                                            -- ζ regular at 0
          HasDerivAt z (e₂τ θ σ / e₁ θ σ) σ ∧ 2 * r₀ < |e₂τ θ σ / e₁ θ σ| ∧   -- zero steeper
          |e₁ θ σ| ≤ K₁ * |θ| * σ ∧                                    -- than the pole
          ∃ α ratio : ℝ, α ≠ 0 ∧ dtwin (a θ σ) (b θ σ) (a' θ σ) (b' θ σ) σ ≠ 0 ∧
            Tendsto (fun τ => twin sStar a b θ τ / z τ) (𝓝[≠] σ) (𝓝 ratio) ∧
            ratio = dtwin (a θ σ) (b θ σ) (a' θ σ) (b' θ σ) σ / α ∧ ratio ≠ 1 ∧
            R σ = τR * ratio ∧ R σ ≠ τR ∧                              -- ζ(0;g_σ) ≠ τ_R
            refinedTorsion 1 (dtwin (a θ σ) (b θ σ) (a' θ σ) (b' θ σ) σ /
              (α - dtwin (a θ σ) (b θ σ) (a' θ σ) (b' θ σ) σ)) =
              -(α / dtwin (a θ σ) (b θ σ) (a' θ σ) (b' θ σ) σ) := by   -- Lemma A
  intro a b r₀
  have hM00 : M' 0 0 = Nmat Bcc Bcψ Bψc Bψψ p := Nmat_unique h422.det_ne _ h422.eq422
  have ha0 : a 0 0 = r₀ := by
    change (Ndiv M M' sStar 0 0).trace = _
    rw [Ndiv_zero, hM00, trace_Nmat]
  have hb0 : b 0 0 = 0 := by
    change (Ndiv M M' sStar 0 0).det = 0
    rw [Ndiv_zero, hM00, det_Nmat]
  have hcont_a : ContinuousAt (Function.uncurry a) (0, 0) :=
    continuousAt_trace_Ndiv M M' sStar hsemisimple hclusterC1.deriv hclusterC1.cont
  have hcont_b : ContinuousAt (Function.uncurry b) (0, 0) :=
    continuousAt_det_Ndiv M M' sStar hsemisimple hclusterC1.deriv hclusterC1.cont
  obtain ⟨θ₀, δ, hθ₀, hδ, H⟩ :=
    fried_fails_at_crossing_of_pure_zero_inputs (K := K) (V₁ := V₁) (V₂ := V₂) (V₃ := V₃)
      sStar a b a' b' hr₀ htraceDetC1.deriv_a htraceDetC1.deriv_b hcont_a hcont_b
      htraceDetC1.cont_a' htraceDetC1.cont_b' ha0 hb0
      hdouble.zero hdouble.cont hdouble.neg e₁ e₂ e₁τ e₁θτ e₂τ e₂ττ e₂θττ
      hpureSumC2.K_pos hpureProdC3.K_pos hpureSumC2.ε_pos
      hpureSumC2.deriv_τ hpureSumC2.deriv_θτ hpureSumC2.bound
      hpureProdC3.deriv_τ hpureProdC3.deriv_ττ hpureProdC3.deriv_θττ hpureProdC3.bound
      hmirror_sum hpinning.sum hmirror_prod hpinning.prod
  refine ⟨θ₀, δ, hθ₀, hδ, fun θ hθne hθ z R c τR hτR hzQ hbranch hexactZero hgeneric hregular
    hfried_off hexact hacyc hdual hdims => ?_⟩
  exact H θ hθne hθ z R c τR hτR hzQ
    (fun τ₀ hτ₀ h0 => ⟨(hbranch τ₀ hτ₀ h0).1, (hbranch τ₀ hτ₀ h0).2, hexactZero τ₀ hτ₀ h0,
      hgeneric τ₀ hτ₀ h0⟩)
    hregular hfried_off hexact hacyc hdual hdims

end FriedCrossing

/-! The certificate: the build log prints the axioms the statement depends on. Expected:
`[propext, Classical.choice, Quot.sound]` — Lean's built-ins, nothing of ours. -/
#print axioms FriedCrossing.fried_counterexample_of_inputs
