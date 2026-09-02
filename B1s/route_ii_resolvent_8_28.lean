/-
ROUTE (ii) AT RESOLVENT/HOLOMORPHIC GRADE (8/28) — approach B of the three-sibling
route-(ii) split (A = attainment/topological spectral-set grade; C = correlation/
quantitative-interchange grade). One file for this leg, per the one-file-per-leg scheme.

Context (Front Page ¶3): route (ii) DERIVES the endpoint clause of H — a twisted
resonance-free strip for the geodesic flow at b = ∞ — from open-interval uniformity,
instead of assuming it. Pollicott–Ruelle resonances are poles of meromorphically
continued resolvents on anisotropic spaces; this file proves the holomorphic-analysis
spine: uniform bounds + convergence of holomorphic functions force the limit to be
holomorphic and locally bounded on the strip Ω, hence POLE-FREE there.

⚡GRADE WARNING (why every statement is for SCALAR functions ℂ → ℂ): at b = ∞ the
twisted geodesic-flow semigroup is an ISOMETRY on L² (volume-preserving flow, unitary
twist), so no L² operator-norm decay survives the limit. The objects that DO survive
at this grade are scalar MATRIX ELEMENTS of resolvents,
    f_b(z) = ⟨R_b(z) u, v⟩   for fixed nice vectors u, v
(and their limits, matrix elements of the meromorphically continued flow resolvent on
the anisotropic space). Every `F : ℝ → ℂ → ℂ` below is such a family, indexed by
b ∈ ℝ along `atTop`; the operator-level clause of H enters only through the scalar
hypotheses it implies for these matrix elements. A pole of the continued resolvent at
z₀ is visible in SOME matrix element (anisotropic-space duality pairs the residue
projector nontrivially), so pole-freeness of every f is pole-freeness of the resolvent.
(Sibling C's route_ii_correlation_8_28.lean machine-checks this warning as a negative
theorem: uniform-C operator decay + the isometric endpoint is contradictory.)

⚡RESEARCH ANSWER (the deliverable of this leg's research question): Mathlib does NOT
have the Montel/Vitali upgrade. Grepped .lake/packages/mathlib 8/28:
  - "Montel" hits only Mathlib/Analysis/LocallyConvex/Montel.lean = Montel SPACES
    (TVS Heine–Borel property; Trèves Prop 34.5) — not normal families;
  - no complex-analytic Vitali convergence theorem (the "Vitali" hits are the
    covering-theorem family);
  - Ascoli exists (Topology/UniformSpace/Ascoli.lean) but the Cauchy-estimate
    equicontinuity of a locally bounded holomorphic family is nowhere, so the upgrade
    pointwise + local uniform bound ⇒ locally uniform convergence (along the full
    filter or a subfilter) is NOT available and is a real project to build.
CONSEQUENCE for read #3: `h_conv` must enter at `TendstoLocallyUniformlyOn` grade —
the exact citation shape route (ii) demands from stochastic stability [Drouot, [C],
twisted scope flagged] is LOCALLY UNIFORM (compact-set-uniform) convergence of
resolvent matrix elements on the strip, not merely pointwise convergence. Drouot's
resolvent convergence is norm-convergence on compacts away from limit resonances,
which restricts to exactly this scalar shape, so the demand is expected to be met —
but it is the thing to CHECK, and this file is the machine ledger of why pointwise
would not suffice (`limit_locallyBounded_ofPointwise` shows what pointwise DOES buy:
conclusion (ii) but not (i)).

What is proved (zero axioms; citations enter only as named hypotheses):
  limit_differentiableOn      — (i) the limit matrix element is holomorphic on Ω
                                (consumes Mathlib's Weierstrass theorem
                                `TendstoLocallyUniformlyOn.differentiableOn`).
  locallyBounded_of_tlu       — (ii) the limit is locally bounded on Ω; at loc-unif
                                grade this is FREE (no separate bound hypothesis).
  uniform_bound_of_tlu        — ⚡LEDGER FACT the informal sketch missed: at loc-unif
                                convergence grade the uniform-local-bound clause
                                (h_bdd, "H at this grade") is DERIVABLE, not an
                                input — the b-uniform bound on compacts holds
                                eventually for the family itself. H's load therefore
                                rests entirely on h_holo + h_conv (see docstrings).
  limit_locallyBounded_ofPointwise
                              — (ii) again at POINTWISE grade + explicit h_bdd: the
                                complementary ledger entry (what survives if read #3
                                only certifies pointwise convergence).
  no_pole_of_locallyBounded   — (iii) THE NO-POLE BRIDGE: a function agreeing with f
                                near z₀ (off z₀) cannot blow up at z₀ if f is locally
                                bounded. ⚡Holomorphy of g is NOT consumed — the
                                contradiction is purely metric; stated so the ledger
                                shows pole-freeness at this grade needs only
                                agreement + local boundedness.
  blowup_of_tendsto_atTop     — a genuine pole (‖g‖ → ∞ along 𝓝[≠] z₀) satisfies the
                                blow-up hypothesis (uses ℂ having no isolated points).
  route_ii_resolvent          — THE ASSEMBLED THEOREM OF THIS LEG: from h_holo + h_conv
                                alone, conclusions (i) + (ii) + (iii) on all of Ω.
  route_ii_no_pole            — corollary in genuine-pole form: no point of Ω is a
                                pole of any continuation of f.
-/
import Mathlib

set_option linter.style.header false

namespace FriedRouteIIB

open Filter Topology Metric

/-! ### §1 Conclusion (i): the limit is holomorphic on the strip -/

/-- (i) HOLOMORPHY OF THE LIMIT. `F b` = the scalar matrix element z ↦ ⟨R_b(z) u, v⟩
of the kinetic resolvent; `f` = its b → ∞ limit; `Ω` = the open strip/half-plane
{Re z > -β} (any open set works). Hypothesis ↦ citation map:
  `h_holo` — eventually in b, F b is holomorphic on Ω. THIS IS WHERE H'S UNIFORM GAP
             IS SPENT at this grade: the resolvent b ↦ R_b(z) is holomorphic precisely
             off spec(L_b), and H keeps spec(L_b) out of the strip eventually in b
             (Front Page: "uniform-gap H keeps those eigenvalues out of {Re λ < β}").
  `h_conv` — locally uniform convergence of the matrix elements on Ω: the stochastic-
             stability citation [Drouot, [C], twisted scope = read #3], demanded at
             EXACTLY this grade because Mathlib has no Montel/Vitali upgrade from
             pointwise (see file header).
Consumes Mathlib's Weierstrass convergence theorem. -/
theorem limit_differentiableOn (F : ℝ → ℂ → ℂ) (f : ℂ → ℂ) (Ω : Set ℂ)
    (hΩ : IsOpen Ω)
    (h_holo : ∀ᶠ b in atTop, DifferentiableOn ℂ (F b) Ω)
    (h_conv : TendstoLocallyUniformlyOn F f atTop Ω) :
    DifferentiableOn ℂ f Ω :=
  h_conv.differentiableOn h_holo hΩ

/-! ### §2 Conclusion (ii): local boundedness — at both grades -/

/-- (ii) at locally-uniform grade: the limit is bounded on every compact K ⊆ Ω.
FREE given §1 — continuity of the holomorphic limit on a compact. No bound hypothesis
on the family is consumed; compare `limit_locallyBounded_ofPointwise`. -/
theorem locallyBounded_of_tlu (F : ℝ → ℂ → ℂ) (f : ℂ → ℂ) (Ω : Set ℂ)
    (hΩ : IsOpen Ω)
    (h_holo : ∀ᶠ b in atTop, DifferentiableOn ℂ (F b) Ω)
    (h_conv : TendstoLocallyUniformlyOn F f atTop Ω) :
    ∀ K ⊆ Ω, IsCompact K → ∃ M, ∀ z ∈ K, ‖f z‖ ≤ M := by
  intro K hKΩ hK
  have hf : DifferentiableOn ℂ f Ω := h_conv.differentiableOn h_holo hΩ
  exact hK.exists_bound_of_continuousOn (hf.continuousOn.mono hKΩ)

/-- ⚡LEDGER: at locally-uniform convergence grade, the UNIFORM FAMILY BOUND — the
clause one would state as "H at resolvent grade" (for every compact K ⊆ Ω there is M
with, eventually in b, ‖F b z‖ ≤ M on K) — is DERIVABLE from h_holo + h_conv, with
the same M bounding the limit. So the citation shape of read #3 (loc-unif convergence)
subsumes the uniform-bound clause; stating both as inputs would double-count H. The
informal route-(ii) sketch listed them as separate inputs — this is the correction. -/
theorem uniform_bound_of_tlu (F : ℝ → ℂ → ℂ) (f : ℂ → ℂ) (Ω : Set ℂ)
    (hΩ : IsOpen Ω)
    (h_holo : ∀ᶠ b in atTop, DifferentiableOn ℂ (F b) Ω)
    (h_conv : TendstoLocallyUniformlyOn F f atTop Ω) :
    ∀ K ⊆ Ω, IsCompact K → ∃ M,
      (∀ᶠ b in atTop, ∀ z ∈ K, ‖F b z‖ ≤ M) ∧ ∀ z ∈ K, ‖f z‖ ≤ M := by
  intro K hKΩ hK
  have hf : DifferentiableOn ℂ f Ω := h_conv.differentiableOn h_holo hΩ
  obtain ⟨M₀, hM₀⟩ := hK.exists_bound_of_continuousOn (hf.continuousOn.mono hKΩ)
  have hu : TendstoUniformlyOn F f atTop K :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hΩ).mp h_conv K hKΩ hK
  have hev : ∀ᶠ b in atTop, ∀ z ∈ K, dist (f z) (F b z) < 1 :=
    Metric.tendstoUniformlyOn_iff.mp hu 1 one_pos
  refine ⟨M₀ + 1, ?_, fun z hz => le_trans (hM₀ z hz) (by linarith)⟩
  filter_upwards [hev] with b hb z hz
  have h1 : ‖F b z‖ - ‖f z‖ ≤ ‖F b z - f z‖ := norm_sub_norm_le _ _
  have h2 : ‖F b z - f z‖ = dist (f z) (F b z) := by
    rw [dist_eq_norm, norm_sub_rev]
  linarith [hM₀ z hz, hb z hz]

/-- (ii) at POINTWISE grade: if read #3 certifies only pointwise convergence of matrix
elements, conclusion (ii) still holds PROVIDED the uniform local bound `h_bdd` is
supplied separately — and then h_bdd is genuinely H's resolvent-grade clause:
  `h_bdd`  — uniform local bound: H's gap gives ‖R_b(z)‖ ≤ C/dist(z, spec) uniformly
             on compacts of the strip, hence |⟨R_b(z)u, v⟩| ≤ M := C'‖u‖‖v‖ there.
  `h_conv` — pointwise convergence on Ω [Drouot at pointwise grade].
Conclusion (i) is NOT recoverable at this grade inside Mathlib (no Montel/Vitali —
file header), which is exactly why the research note must demand loc-unif from the
literature; this theorem records the fallback perimeter. -/
theorem limit_locallyBounded_ofPointwise (F : ℝ → ℂ → ℂ) (f : ℂ → ℂ) (Ω : Set ℂ)
    (h_bdd : ∀ K ⊆ Ω, IsCompact K → ∃ M, ∀ᶠ b in atTop, ∀ z ∈ K, ‖F b z‖ ≤ M)
    (h_conv : ∀ z ∈ Ω, Tendsto (fun b => F b z) atTop (𝓝 (f z))) :
    ∀ K ⊆ Ω, IsCompact K → ∃ M, ∀ z ∈ K, ‖f z‖ ≤ M := by
  intro K hKΩ hK
  obtain ⟨M, hM⟩ := h_bdd K hKΩ hK
  refine ⟨M, fun z hz => ?_⟩
  have ht : Tendsto (fun b => ‖F b z‖) atTop (𝓝 ‖f z‖) := (h_conv z (hKΩ hz)).norm
  exact le_of_tendsto ht (by filter_upwards [hM] with b hb using hb z hz)

/-! ### §3 Conclusion (iii): the no-pole bridge -/

/-- (iii) THE NO-POLE BRIDGE. Formal rendering of "f has no pole at z₀ ∈ Ω": if g
agrees with f on a punctured neighborhood of z₀ (`h_agree` — g is any meromorphic-
continuation candidate, e.g. the anisotropic-space continued resolvent matrix element,
whose poles are the PR resonances) and ‖g‖ is unbounded near z₀ in the frequently
sense (`h_blowup` — the pole-like clause; weaker than a genuine pole, so this also
excludes essential-type blow-up), then f being locally bounded on Ω (`h_locbdd` =
conclusion (ii)) is contradicted. ⚡Holomorphy of g is deliberately NOT a hypothesis:
the contradiction is metric, so the machine ledger shows pole-freeness at this grade
consumes no analyticity of the continuation — only agreement + local boundedness. -/
theorem no_pole_of_locallyBounded (f g : ℂ → ℂ) (Ω : Set ℂ) (z₀ : ℂ)
    (hΩ : IsOpen Ω) (hz₀ : z₀ ∈ Ω)
    (h_locbdd : ∀ K ⊆ Ω, IsCompact K → ∃ M, ∀ z ∈ K, ‖f z‖ ≤ M)
    (h_agree : ∀ᶠ z in 𝓝[≠] z₀, g z = f z)
    (h_blowup : ∀ M : ℝ, ∃ᶠ z in 𝓝[≠] z₀, M < ‖g z‖) :
    False := by
  obtain ⟨r, hr, hrΩ⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hΩ.mem_nhds hz₀)
  obtain ⟨M, hM⟩ := h_locbdd (closedBall z₀ r) hrΩ (isCompact_closedBall z₀ r)
  have hball : ∀ᶠ z in 𝓝[≠] z₀, z ∈ closedBall z₀ r :=
    mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds z₀ hr)
  obtain ⟨z, hzM, hzf, hzK⟩ := ((h_blowup M).and_eventually (h_agree.and hball)).exists
  rw [hzf] at hzM
  exact absurd (hM z hzK) (not_le.mpr hzM)

/-- A genuine pole implies the frequently-blow-up clause: if ‖g‖ → ∞ along the
punctured neighborhood filter, then for every M, ‖g‖ > M frequently near z₀.
Uses that ℂ has no isolated points (𝓝[≠] z₀ ≠ ⊥). -/
theorem blowup_of_tendsto_atTop (g : ℂ → ℂ) (z₀ : ℂ)
    (h : Tendsto (fun z => ‖g z‖) (𝓝[≠] z₀) atTop) :
    ∀ M : ℝ, ∃ᶠ z in 𝓝[≠] z₀, M < ‖g z‖ :=
  fun M => (h.eventually (eventually_gt_atTop M)).frequently

/-! ### §4 The assembled route-(ii) theorem at this grade -/

/-- ROUTE (ii), RESOLVENT GRADE, ASSEMBLED. From exactly two named inputs —
  `h_holo` (H's uniform gap: eventual holomorphy of the resolvent matrix elements on
            the strip) and
  `h_conv` (stochastic stability [Drouot, [C], twisted flag] at locally-uniform grade
            — the demanded citation shape, since Mathlib has no Montel/Vitali) —
the limit matrix element is (i) holomorphic on Ω, (ii) locally bounded on Ω, and
(iii) pole-free: no continuation g of f off any z₀ ∈ Ω can blow up at z₀. Instantiated
with Ω = the strip {−β < Re z < 0}-side region and f = the continued flow-resolvent
matrix elements, (iii) says NO Pollicott–Ruelle resonance lies in the strip — the
endpoint clause of H, DERIVED.
⚡RELATION TO SIBLING A (attainment/topological grade): at math level, loc-unif
convergence of resolvent matrix elements IMPLIES A's spectral attainment via the
argument principle/Hurwitz (zeros/poles of loc-unif limits are limits of zeros/poles)
— remark only, not formalized here; A consumes attainment as its own citation. -/
theorem route_ii_resolvent (F : ℝ → ℂ → ℂ) (f : ℂ → ℂ) (Ω : Set ℂ)
    (hΩ : IsOpen Ω)
    (h_holo : ∀ᶠ b in atTop, DifferentiableOn ℂ (F b) Ω)
    (h_conv : TendstoLocallyUniformlyOn F f atTop Ω) :
    DifferentiableOn ℂ f Ω ∧
      (∀ K ⊆ Ω, IsCompact K → ∃ M, ∀ z ∈ K, ‖f z‖ ≤ M) ∧
      ∀ z₀ ∈ Ω, ∀ g : ℂ → ℂ, (∀ᶠ z in 𝓝[≠] z₀, g z = f z) →
        ¬ ∀ M : ℝ, ∃ᶠ z in 𝓝[≠] z₀, M < ‖g z‖ := by
  refine ⟨limit_differentiableOn F f Ω hΩ h_holo h_conv,
    locallyBounded_of_tlu F f Ω hΩ h_holo h_conv, ?_⟩
  intro z₀ hz₀ g h_agree h_blowup
  exact no_pole_of_locallyBounded f g Ω z₀ hΩ hz₀
    (locallyBounded_of_tlu F f Ω hΩ h_holo h_conv) h_agree h_blowup

/-- Corollary in genuine-pole form: under the same two inputs, no z₀ ∈ Ω is a pole of
any continuation of f — the resonance-free strip, in the form the note quotes. -/
theorem route_ii_no_pole (F : ℝ → ℂ → ℂ) (f : ℂ → ℂ) (Ω : Set ℂ)
    (hΩ : IsOpen Ω)
    (h_holo : ∀ᶠ b in atTop, DifferentiableOn ℂ (F b) Ω)
    (h_conv : TendstoLocallyUniformlyOn F f atTop Ω) :
    ∀ z₀ ∈ Ω, ∀ g : ℂ → ℂ, (∀ᶠ z in 𝓝[≠] z₀, g z = f z) →
      ¬ Tendsto (fun z => ‖g z‖) (𝓝[≠] z₀) atTop := by
  intro z₀ hz₀ g h_agree h
  exact (route_ii_resolvent F f Ω hΩ h_holo h_conv).2.2 z₀ hz₀ g h_agree
    (blowup_of_tendsto_atTop g z₀ h)

end FriedRouteIIB
