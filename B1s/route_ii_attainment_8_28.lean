/-
ROUTE (ii), APPROACH A — ATTAINMENT / TOPOLOGICAL GRADE (8/28). One of three sibling
files on route (ii) (B = resolvent/holomorphic-limit grade; C = correlation/
quantitative-interchange grade). Context: Front Page ¶3 — derive the ENDPOINT CLAUSE
of H (the b = ∞ twisted resonance-free strip for the geodesic flow) from
open-interval uniformity, instead of assuming it.

⚡GRADE WARNING (why every statement here is about SETS, never operators): at b = ∞
the twisted geodesic-flow semigroup is an ISOMETRY on L² (volume-preserving flow,
unitary twist), so NO L² operator-norm decay passes to the limit; Σ∞ lives on
anisotropic spaces. This file therefore works at SPECTRAL-SET grade: spectra are
subsets of ℂ and the citations are hypotheses about those subsets. H itself is
operator-norm grade at finite b; the standard implication "uniform semigroup bound
⇒ spectral inclusion" (Hille–Yosida-grade, [B]) is consumed BEFORE this file, so
`h_gap` below is H's spectral-set shadow.

The informal 4-step sketch and where each step lands here:
  (1) essential-gap theorem [twisted essential-gap citation — the axis-clearing
      killer item]: only finitely many elements of Σ∞ in {Re z < β₀}.
      ⚡FINDING (research question a): FINITENESS IS NOT CONSUMED at this grade.
      Its only surviving role is SCOPE: it is what makes Σ∞ ∩ {Re z < β₀} a
      discrete (finite-multiplicity) set, i.e. the region where Drouot-attainment
      is CITABLE at all. It enters the theorems below solely as the restriction
      `z.re < β₀` on `h_attain`, hence the `min β β₀` in the conclusions —
      never as a Set.Finite hypothesis. `endpointClause_informalShape` carries
      the Finite hypothesis with a `_`-prefixed name to make the non-consumption
      machine-visible (the m1Consumption/negCurv pattern of endpoints_8_20).
  (2) stochastic stability [Drouot, [C], twisted scope = read #3]: `h_attain` —
      every element of Σ∞ (in the citable region) is attained: every neighborhood
      of it eventually meets the approximant spectrum Spec b.
  (3) H (uniform gap, spectral-set shadow): `h_gap` — eventually in b,
      Spec b ∩ {Re z < β} = ∅.
  (4) combine: Σ∞ ∩ {Re z < min β β₀} = ∅ — the endpoint clause.

File plan:
  endpointClause_ofAttainment    — THE MAIN THEOREM: per-point attainment on the
                                   citable region + eventual gap ⇒ endpoint clause
                                   at min β β₀.
  endpointClause_ofAttainment_unrestricted
                                 — β₀ scope dropped (attainment on all of Σ∞) ⇒
                                   clause at β itself: what per-point attainment
                                   alone buys, with NO essential-gap citation.
  attainment_ofCompactAttainment — bridge: the HONEST citation form (attainment
                                   uniform on compacts, b-threshold depending on
                                   the compact, metric-ball error) implies the
                                   per-point form — via the SINGLETON compact.
  endpointClause_ofCompactAttainment
                                 — research question (b): the compact-thresholded
                                   form still suffices; composition of the two.
  endpointClause_informalShape   — the 4-step sketch verbatim, finiteness carried
                                   but visibly unconsumed.
-/
import Mathlib

set_option linter.style.header false

namespace FriedRouteIIA

open Filter Topology Set

/-! ### §1 The main theorem: per-point attainment + eventual gap ⇒ endpoint clause

`Spec : ℝ → Set ℂ` — the spectrum of L_b as a SUBSET of ℂ (kinetic operator on the
ρ-twisted complex; which space it acts on is deliberately forgotten — set grade).
`SpecInf : Set ℂ` — Σ∞, the Pollicott–Ruelle resonance set of the twisted geodesic
flow (the b = ∞ member, living on anisotropic spaces — set grade again). -/

/-- ROUTE (ii) MAIN THEOREM (attainment grade). Hypotheses = the two citations:

`h_attain` — [Drouot stochastic stability, [C], twisted extension flagged, read #3]:
every z ∈ Σ∞ in the citable region {Re z < β₀} is ATTAINED — every neighborhood U
of z eventually meets Spec b as b → ∞. The restriction `z.re < β₀` is the ONLY
trace of the essential-gap citation: it delimits where Σ∞ is discrete, hence where
Drouot's theorem applies. NO finiteness is consumed (research finding (a)).

`h_gap` — [H, the program's hypothesis, spectral-set shadow]: eventually in b, the
spectrum of L_b avoids the open half-plane {Re z < β}. H's operator-norm content
(uniform semigroup bound) is spent upstream converting to this set statement.

CONCLUSION — the endpoint clause, DERIVED: Σ∞ avoids {Re z < min β β₀}.

Proof shape: if z ∈ Σ∞ had Re z < min β β₀, the open half-plane {Re w < β} is
itself a neighborhood of z; attainment makes Spec b meet it eventually, the gap
empties it eventually, and atTop is NeBot — contradiction at a common b.

RELATION TO SIBLING B's GRADE (remark only, not formalized): B's citation shape —
locally-uniform convergence of resolvents / their matrix elements
(`TendstoLocallyUniformlyOn`) — implies THIS file's `h_attain` at math level via
the argument principle/Hurwitz: a resonance z ∈ Σ∞ is a zero (pole) of the limit
holomorphic datum, so by Hurwitz every small disc around z eventually contains a
zero (pole) of the approximant, i.e. a point of Spec b. So the two files consume
the SAME Drouot citation at adjacent grades, B's shape ⇒ A's shape. -/
theorem endpointClause_ofAttainment (Spec : ℝ → Set ℂ) (SpecInf : Set ℂ) (β β₀ : ℝ)
    (h_attain : ∀ z ∈ SpecInf, z.re < β₀ →
      ∀ U ∈ 𝓝 z, ∀ᶠ b in atTop, (Spec b ∩ U).Nonempty)
    (h_gap : ∀ᶠ b in atTop, Spec b ∩ {w : ℂ | w.re < β} = ∅) :
    SpecInf ∩ {z : ℂ | z.re < min β β₀} = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro z ⟨hzInf, hzlt⟩
  have hzβ : z.re < β := lt_of_lt_of_le hzlt (min_le_left _ _)
  have hzβ₀ : z.re < β₀ := lt_of_lt_of_le hzlt (min_le_right _ _)
  have hUopen : IsOpen {w : ℂ | w.re < β} :=
    isOpen_lt Complex.continuous_re continuous_const
  have hmeet := h_attain z hzInf hzβ₀ _ (hUopen.mem_nhds hzβ)
  obtain ⟨b, hne, hempty⟩ := (hmeet.and h_gap).exists
  rw [hempty] at hne
  exact Set.not_nonempty_empty hne

/-- Research finding (a), isolated: with attainment citable on ALL of Σ∞ (no
essential-gap scoping), per-point attainment ALONE closes the argument at β itself
— no finiteness, no β₀, no second citation. If Drouot's twisted statement can be
read with neighborhoods of arbitrary resonances (it can wherever Σ∞ is discrete),
the research note needs ONLY [Drouot] + [H] for the endpoint clause on the full
gap strip. -/
theorem endpointClause_ofAttainment_unrestricted (Spec : ℝ → Set ℂ)
    (SpecInf : Set ℂ) (β : ℝ)
    (h_attain : ∀ z ∈ SpecInf, ∀ U ∈ 𝓝 z, ∀ᶠ b in atTop, (Spec b ∩ U).Nonempty)
    (h_gap : ∀ᶠ b in atTop, Spec b ∩ {w : ℂ | w.re < β} = ∅) :
    SpecInf ∩ {z : ℂ | z.re < β} = ∅ := by
  have h := endpointClause_ofAttainment Spec SpecInf β β
    (fun z hz _ => h_attain z hz) h_gap
  simpa [min_self] using h

/-! ### §2 Research question (b): the compact-thresholded citation form -/

/-- BRIDGE (the content of research answer (b)): the HONEST citation shape —
attainment uniform over a compact K, with the b-threshold depending on K and the
error measured in metric balls (`dist w z < ε`), i.e. "resonances in a compact set
are approximated, locally uniformly, thresholds per compact" — IMPLIES the
per-point neighborhood form of §1. The proof instantiates K := {z} (singletons are
compact) and shrinks U to a metric ball; NOTHING about larger compacts, covers, or
uniformity over K is used. So the compact-thresholded form suffices, and the
formalization shows WHY with precision: route (ii) consumes Drouot only at
singleton compacts — one point, one ball, one threshold. -/
theorem attainment_ofCompactAttainment (Spec : ℝ → Set ℂ) (SpecInf : Set ℂ)
    (β₀ : ℝ)
    (h_attainK : ∀ K : Set ℂ, IsCompact K → ∀ ε > 0, ∀ᶠ b in atTop,
      ∀ z ∈ SpecInf ∩ K, z.re < β₀ → ∃ w ∈ Spec b, dist w z < ε) :
    ∀ z ∈ SpecInf, z.re < β₀ →
      ∀ U ∈ 𝓝 z, ∀ᶠ b in atTop, (Spec b ∩ U).Nonempty := by
  intro z hz hzβ₀ U hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  filter_upwards [h_attainK {z} isCompact_singleton ε hε] with b hb
  obtain ⟨w, hwSpec, hwdist⟩ := hb z ⟨hz, rfl⟩ hzβ₀
  exact ⟨w, hwSpec, hball (Metric.mem_ball.mpr hwdist)⟩

/-- ROUTE (ii) AT THE HONEST CITATION GRADE (research answer (b)): the
compact-thresholded attainment form still yields the endpoint clause — it does NOT
fail. Composition of `attainment_ofCompactAttainment` with
`endpointClause_ofAttainment`. The research note may therefore cite Drouot in the
locally-uniform-on-compacts form he proves, with no strengthening. -/
theorem endpointClause_ofCompactAttainment (Spec : ℝ → Set ℂ) (SpecInf : Set ℂ)
    (β β₀ : ℝ)
    (h_attainK : ∀ K : Set ℂ, IsCompact K → ∀ ε > 0, ∀ᶠ b in atTop,
      ∀ z ∈ SpecInf ∩ K, z.re < β₀ → ∃ w ∈ Spec b, dist w z < ε)
    (h_gap : ∀ᶠ b in atTop, Spec b ∩ {w : ℂ | w.re < β} = ∅) :
    SpecInf ∩ {z : ℂ | z.re < min β β₀} = ∅ :=
  endpointClause_ofAttainment Spec SpecInf β β₀
    (attainment_ofCompactAttainment Spec SpecInf β₀ h_attainK) h_gap

/-! ### §3 The informal 4-step sketch, verbatim — finiteness visibly unconsumed -/

/-- THE SKETCH AS STATED (fidelity theorem). Carries all four steps' hypotheses in
the shapes the informal argument lists them, INCLUDING step (1)'s finiteness —
named `_h_finite` with the underscore prefix because it is DELIBERATELY UNUSED
(the machine-visible non-consumption pattern of endpoints_8_20's `m1Consumption`,
where `ns.neg` is the unconsumed field). ⚡Ledger fact this theorem records: the
essential-gap theorem's FINITENESS conclusion is not what route (ii) spends; only
its SCOPE (discreteness of Σ∞ below β₀, which licenses citing `h_attain` there)
survives, as the β₀ in `min β β₀`. -/
theorem endpointClause_informalShape (Spec : ℝ → Set ℂ) (SpecInf : Set ℂ)
    (β β₀ : ℝ)
    (_h_finite : {z ∈ SpecInf | z.re < β₀}.Finite)
    (h_attain : ∀ z ∈ SpecInf, z.re < β₀ →
      ∀ U ∈ 𝓝 z, ∀ᶠ b in atTop, (Spec b ∩ U).Nonempty)
    (h_gap : ∀ᶠ b in atTop, Spec b ∩ {w : ℂ | w.re < β} = ∅) :
    SpecInf ∩ {z : ℂ | z.re < min β β₀} = ∅ :=
  endpointClause_ofAttainment Spec SpecInf β β₀ h_attain h_gap

end FriedRouteIIA
