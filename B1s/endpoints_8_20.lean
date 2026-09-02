/-
THE ENDPOINTS — M1 + V2 INTERFACE AND THE TOP-LEVEL GLUE (8/20, per Ben: "how much of
M1 can be done in Lean?"). One file for the endpoint leg, per the one-file-per-leg
scheme (b1_spectral = B1 · object_matching_s1 = obj-match · bridge_8_20 = bridge).
Context: obligations M1 (#3) and V2 (#5) of note_preflight_8_15.md. The ~0.07 top-killer
risk is NOT that Bismut–Lebeau's theorem is false — it is that WE mis-consume it
(scope/conventions/transcription). This file machine-checks the consumption surface:

  endpointGlue       — THE TOP-LEVEL THEOREM OF THE NOTE, fully proved: a quantity
                       constant on (0, ∞) (legs 2+4: bridge + budget), whose b → 0⁺
                       limit is torsion (leg 5a: M1/BL citation) and whose b → ∞ limit
                       is the zeta reading (leg 5b: V2 citation), forces
                       torsion = zeta. Zero axioms — genuine Mathlib analysis.
  endpointGlueValue  — the constant itself equals both endpoint values.
  BLTorsionHypotheses / NoteSetting / m1Consumption
                     — the TYPED CHECKLIST for the M1 read: BL's requirements and our
                       setting as named fields; consumption = a field mapping. When the
                       read fills each ⚡TO-FILL slot with the book's actual condition,
                       any scope mismatch becomes a TYPE ERROR, not a prose oversight.
                       ⚡Machine-visible ledger fact: the b → 0 endpoint consumes NO
                       curvature hypothesis — `NoteSetting`'s negCurv field is
                       deliberately unused by `m1Consumption`; curvature is spent only
                       at the flow end (V2 / hypothesis side).

What CANNOT go in Lean (and why that costs no risk): BL's b → 0 analysis itself —
the resolvent/heat apparatus behind hypoelliptic torsion. That is their proven theorem;
its truth is not our exposure. Our exposure is the interface, and the interface is what
this file types. ⚡TO-FILL checklist for the M1 read (mirrors the fields below):
  [x] exact theorem number(s): Thm 8.2.1 (small-b comparison; both correction terms
      vanish for acyclic ρ on odd-dim X — 8/25 photo) + Thm 6.7.1 ("the generalized
      metric does not depend on b", all b > 0 via the §6.4 Quillen truncation — 8/26
      photos). T_hypo(b) = T_RS unconditional, all b > 0.
  [ ] bundle scope: Thm 8.2.1's display = arbitrary flat (∇^F, g^F) incl. duals and
      o(TX)-twists; ⚡the §1.1–1.2 F-conventions block is the LAST unsighted hop
      (ch. 4 → ch. 2 → §1.2 chain, 8/27 photo) — rides with the C1 photo.
      `hbundle` is the SOLE remaining TO-FILL argument.
  [x] b-range: ALL b > 0 (Thm 6.7.1 + Def 6.4.1 truncation; A3 CLOSED 8/26) —
      `hb` is now trivial membership in Ioi 0.
  [x] metric assumptions: CONFIRMED NONE beyond compact Riemannian — ch. 2 preamble
      photo 8/27, verbatim "In particular X denotes a compact Riemannian manifold of
      dimension n"; no curvature hypotheses; completeness moot.
  [ ] convention normalizations (c = 1/b² [+ case confirmed 8/25], factor 2 in 2𝔄²,
      K_b vs r_b, time normalization, □^X/4 — dictionary in
      bl_operator_transcription_8_15.md §3): these become definitional equalities in
      object_matching v2, not here. §2.1 conventions harvested 8/27 (θ = π*p,
      ω = d^{T*X}θ, dv_{T*X}, ℋ, Y^ℋ per [B05 §2]).
-/
import Mathlib
import B1s.b1_spectral_skeleton_8_12

set_option linter.style.header false

namespace FriedEndpoints

open Filter Topology

/-! ### §1 The top-level glue (proved) -/

/-- THE NOTE'S OUTERMOST THEOREM: if the regularized supertrace quantity f is constant
on (0, ∞) — ⚡8/26 UPDATE from the BL read: constancy is now a CITATION, BL Theorem
6.7.1 ("the generalized metric ‖·‖²_{λ,b} does not depend on b", all b > 0, via the
§6.4 Quillen-truncated definition — the rank-N split as BL's own large-b torsion) —
while its b → 0⁺ limit is T (M1: Theorem 8.2.1, corrections vanishing for acyclic ρ on
odd-dim X) and its b → ∞ limit is Z (V2: the flat-trace zeta reading — where H is now
consumed ENTIRELY, fed pre-split into V5a/V5b by BL's own truncation), then T = Z.
Fried is this equality, instantiated. -/
theorem endpointGlue (f : ℝ → ℝ) (c T Z : ℝ)
    (hconst : ∀ b ∈ Set.Ioi (0 : ℝ), f b = c)
    (h0 : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 T))
    (hinf : Tendsto f atTop (𝓝 Z)) :
    T = Z := by
  have hev0 : f =ᶠ[𝓝[>] (0 : ℝ)] fun _ => c :=
    eventually_of_mem self_mem_nhdsWithin fun b hb => hconst b hb
  have hevinf : f =ᶠ[atTop] fun _ => c := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with b hb
    exact hconst b (by simp only [Set.mem_Ioi]; linarith)
  have hc0 : Tendsto (fun _ : ℝ => c) (𝓝[>] (0 : ℝ)) (𝓝 T) := Tendsto.congr' hev0 h0
  have hcinf : Tendsto (fun _ : ℝ => c) atTop (𝓝 Z) := Tendsto.congr' hevinf hinf
  have hT : T = c := tendsto_nhds_unique hc0 tendsto_const_nhds
  have hZ : Z = c := tendsto_nhds_unique hcinf tendsto_const_nhds
  exact hT.trans hZ.symm

/-- The constant equals both endpoint values — the form the note's prose states
("the supertrace quantity IS the torsion, at every b, and IS the zeta value"). -/
theorem endpointGlueValue (f : ℝ → ℝ) (c T : ℝ)
    (hconst : ∀ b ∈ Set.Ioi (0 : ℝ), f b = c)
    (h0 : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 T)) :
    ∀ b ∈ Set.Ioi (0 : ℝ), f b = T := by
  have hev0 : f =ᶠ[𝓝[>] (0 : ℝ)] fun _ => c :=
    eventually_of_mem self_mem_nhdsWithin fun b hb => hconst b hb
  have hc0 : Tendsto (fun _ : ℝ => c) (𝓝[>] (0 : ℝ)) (𝓝 T) := Tendsto.congr' hev0 h0
  have hT : T = c := tendsto_nhds_unique hc0 tendsto_const_nhds
  exact fun b hb => (hconst b hb).trans hT.symm

/-! ### §2 The M1 typed checklist (the consumption interface) -/

/-- Bismut–Lebeau's torsion-theorem requirements, as named fields over parametric Props.
Each ⚡TO-FILL is a checkbox for the M1 read: replace the parameter with the book's
actual printed condition. Logically thin BY DESIGN — the value is the LEDGER: the
consumption theorem below must keep typechecking after every fill. -/
structure BLTorsionHypotheses (Mclosed acyclic bundleScope bRange : Prop) : Prop where
  closed : Mclosed
  acyc : acyclic
  bundle : bundleScope   -- ⚡TO-FILL: unitary required, or arbitrary flat? (survey silent)
  brange : bRange        -- ⚡TO-FILL: all b > 0, or (0, b₀) with geometric b₀?

/-- The note's standing setting (V4 file §1): closed M, negative curvature, ρ unitary
acyclic. Curvature is a field HERE so that its non-use below is machine-visible. -/
structure NoteSetting (Mclosed negCurv acyclic unitaryFlat : Prop) : Prop where
  closed : Mclosed
  neg : negCurv
  acyc : acyclic
  unitary : unitaryFlat

/-- CONSUMPTION: our setting supplies BL's hypotheses. ⚡`ns.neg` (negative curvature)
is NOT consumed — the b → 0 endpoint is curvature-free; curvature is spent only at the
flow end. The two ⚡TO-FILL arguments are the read's deliverables: `hbundle` becomes the
book's scope statement applied to unitarity (identity if unitary suffices; a real
implication if the book covers arbitrary flat); `hb` becomes membership in the book's
actual b-range for the b at which the glue reads the limit.
⚡8/26–27 STATUS: `hb` RESOLVED — the range is all b > 0 (Thm 6.7.1, A3 closed), so
bRange instantiates to membership in Ioi 0, supplied trivially by the glue. `hbundle`
is the sole remaining TO-FILL: Thm 8.2.1's display covers arbitrary flat (∇^F, g^F)
(⇒ trivial implication expected), pending the §1.1–1.2 F-block sighting (the last
unsighted hop of the assumptions chain; ch. 2 preamble sighted 8/27 — geometric side
closed: compact Riemannian, no curvature hypotheses). -/
theorem m1Consumption {Mclosed negCurv acyclic unitaryFlat bundleScope bRange : Prop}
    (ns : NoteSetting Mclosed negCurv acyclic unitaryFlat)
    (hbundle : unitaryFlat → bundleScope)
    (hb : bRange) :
    BLTorsionHypotheses Mclosed acyclic bundleScope bRange :=
  ⟨ns.closed, ns.acyc, hbundle ns.unitary, hb⟩

/-! ### §3 The b → ∞ assembly — ONE named dependency (8/27, per Ben: "can we
reorganize the Lean so that it's in one assumption/dependency?") -/

open FriedB1Spectral in
/-- THE b → ∞ LIMIT, ASSEMBLED (leg 5b). Reduces the b → ∞ reading to exactly two
proof obligations and machine-checks their assembly: to conclude that the spectral
reading F(b) = Σᵢ λᵢ(b)^ℓ converges to the transport reading Σᵢ μᵢ^ℓ, it SUFFICES to
prove, for some choice of rank schedule N(b) → ∞:

  `hfin`  — Σ_{i < N(b)} ‖λᵢ(b)^ℓ − μᵢ^ℓ‖ → 0: the eigenvalue powers below the
            schedule converge to their transport limits, summably. PROOF ROUTE (V5a):
            per-eigenvalue convergence with multiplicity on compact spectral regions
            — stochastic stability, [C] Drouot Thm 5 (scalar, verbatim shape) + [W] bundle-valued
            extension; read #3 DONE 9/01: vault drouot_read_3_9_01.md —
            upgraded to the summed form by the count below the contour being finite
            at each b (V1 trace-class + contour enumeration).
  `htail` — Σ_{i ≥ N(b)} ‖λᵢ(b)‖^ℓ → 0: the spectrum above the schedule contributes
            vanishing total mass. PROOF ROUTE (V5b): hdom — Weyl majorization plus
            the b-tracked singular-value power law ‖λᵢ(b)‖^ℓ ≤ C·b^q·(i+1)^{−αℓ}
            (quantified hypoelliptic smoothing, THE one owed estimate); it discharges
            this clause for ANY schedule N(b) ≫ b^{q/(αℓ−1)}, since then
            C·b^q·Σ_{i≥N(b)}(i+1)^{−αℓ} ≤ C'·b^q·N(b)^{1−αℓ} → 0.

The remaining inputs generate NO obligations: `hrepr` fixes what F is (definition),
`hl`/`hm` are summability of the two power series (V1-grade trace-class facts), `hN`
records that the schedule diverges. The third term of `v5_rank_split`'s bound — the
tail of the LIMIT spectrum — is proved to vanish inside this proof from `hm` and `hN`
via `v5_tail_tendsto`. Downstream: `endpointGlue.hinf` consumes the conclusion, with
the limit identified with the zeta value by V2 (flat-trace citation); constancy (BL
Thm 6.7.1) supplies `hconst`. S¹ model check: s1_truncation_falsifier_8_27.py
(9/9; graded/scaled grade — the reading must be the SUPERTRACE, per T2/T4a). -/
theorem v5_limit_assembly (F : ℝ → ℂ) (lam : ℝ → ℕ → ℂ) (mu : ℕ → ℂ) (ℓ : ℕ)
    (N : ℝ → ℕ)
    (hrepr : ∀ b, F b = ∑' i, lam b i ^ ℓ)
    (hl : ∀ b, Summable fun i => ‖lam b i‖ ^ ℓ)
    (hm : Summable fun i => ‖mu i‖ ^ ℓ)
    (hN : Tendsto N atTop atTop)
    (hfin : Tendsto (fun b => ∑ i ∈ Finset.range (N b), ‖lam b i ^ ℓ - mu i ^ ℓ‖)
      atTop (𝓝 0))
    (htail : Tendsto (fun b => ∑' i, ‖lam b (i + N b)‖ ^ ℓ) atTop (𝓝 0)) :
    Tendsto F atTop (𝓝 (∑' i, mu i ^ ℓ)) := by
  have hbound : ∀ b, ‖F b - ∑' i, mu i ^ ℓ‖ ≤
      (∑ i ∈ Finset.range (N b), ‖lam b i ^ ℓ - mu i ^ ℓ‖)
        + (∑' i, ‖lam b (i + N b)‖ ^ ℓ) + ∑' i, ‖mu (i + N b)‖ ^ ℓ := by
    intro b
    rw [hrepr b]
    exact v5_rank_split (lam b) mu ℓ (N b) (hl b) hm
  have hmu_tail : Tendsto (fun b => ∑' i, ‖mu (i + N b)‖ ^ ℓ) atTop (𝓝 0) := by
    exact (v5_tail_tendsto (fun i => ‖mu i‖ ^ ℓ) hm).comp hN
  have hsum : Tendsto (fun b =>
      (∑ i ∈ Finset.range (N b), ‖lam b i ^ ℓ - mu i ^ ℓ‖)
        + (∑' i, ‖lam b (i + N b)‖ ^ ℓ) + ∑' i, ‖mu (i + N b)‖ ^ ℓ) atTop (𝓝 0) := by
    simpa using (hfin.add htail).add hmu_tail
  exact tendsto_sub_nhds_zero_iff.mp (squeeze_zero_norm hbound hsum)

/-! ### §4 `hfin` reduced to citation shape (8/27 pm, per Ben: "try your strategy
on them") -/

/-- Tails of a summable nonnegative series are antitone in the cut point. -/
theorem tail_anti (t : ℕ → ℝ) (h0 : ∀ i, 0 ≤ t i) (ht : Summable t)
    {N₁ N₂ : ℕ} (h : N₁ ≤ N₂) :
    (∑' i, t (i + N₂)) ≤ ∑' i, t (i + N₁) := by
  have hs : Summable fun i => t (i + N₁) := (summable_nat_add_iff N₁).2 ht
  have key := hs.sum_add_tsum_nat_add (N₂ - N₁)
  have hidx : (fun i => t (i + (N₂ - N₁) + N₁)) = fun i => t (i + N₂) := by
    funext i; congr 1; omega
  rw [hidx] at key
  have hnn : 0 ≤ ∑ i ∈ Finset.range (N₂ - N₁), t (i + N₁) :=
    Finset.sum_nonneg fun i _ => h0 _
  linarith

open FriedB1Spectral in
/-- `v5_limit_assembly` WITH `hfin` AT CITATION SHAPE. The schedule form (§3) asks for
summed drift over growing windows; the analysis will not prove that directly — what
stochastic stability actually provides is PER-EIGENVALUE convergence, `hpt`. This
version consumes exactly that, plus the uniform-tail form of V5b (`htail`: for every
ε there is one FIXED cut N₀ whose λ-tail is eventually ≤ ε — the radius-truncation
grade, where the 8/27 model run measured b-uniform control), and produces the same
conclusion by an ε/4 argument: cut at N = max(N₁, N₂), the finite part → 0 because it
is a FIXED finite sum of vanishing terms (`tendsto_finsetSum`), both tails ≤ ε/4 by
`tail_anti`, and `v5_rank_split` glues. So the two named obligations, in the shape
the literature carries them:
  `hpt`   — λᵢ(b) → μᵢ for each fixed i (resonances converge with multiplicity on
            compacts: Drouot Thm 5 [C, scalar; EXACT shape] + [W] twisted/all-degree extension —
            read #3 9/01, vault drouot_read_3_9_01.md §3);
  `htail` — uniform tail smallness at fixed cuts (hdom at the graded,
            radius-truncated grade — the one owed estimate). -/
theorem v5_limit_assembly_ofPointwise (F : ℝ → ℂ) (lam : ℝ → ℕ → ℂ) (mu : ℕ → ℂ)
    (ℓ : ℕ)
    (hrepr : ∀ b, F b = ∑' i, lam b i ^ ℓ)
    (hl : ∀ b, Summable fun i => ‖lam b i‖ ^ ℓ)
    (hm : Summable fun i => ‖mu i‖ ^ ℓ)
    (hpt : ∀ i, Tendsto (fun b => lam b i) atTop (𝓝 (mu i)))
    (htail : ∀ ε > 0, ∃ N₀ : ℕ, ∀ᶠ b in atTop, (∑' i, ‖lam b (i + N₀)‖ ^ ℓ) ≤ ε) :
    Tendsto F atTop (𝓝 (∑' i, mu i ^ ℓ)) := by
  rw [← tendsto_sub_nhds_zero_iff, NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := htail (ε / 4) (by positivity)
  have hmu0 : Tendsto (fun N => ∑' i, ‖mu (i + N)‖ ^ ℓ) atTop (𝓝 0) :=
    v5_tail_tendsto _ hm
  obtain ⟨N₂, hN₂⟩ :=
    (hmu0.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 4))).exists
  set N := max N₁ N₂ with hNdef
  have hlamnn : ∀ b i, (0 : ℝ) ≤ ‖lam b i‖ ^ ℓ := fun b i => pow_nonneg (norm_nonneg _) _
  have hmunn : ∀ i, (0 : ℝ) ≤ ‖mu i‖ ^ ℓ := fun i => pow_nonneg (norm_nonneg _) _
  have hfin : Tendsto (fun b => ∑ i ∈ Finset.range N, ‖lam b i ^ ℓ - mu i ^ ℓ‖)
      atTop (𝓝 0) := by
    have h := tendsto_finsetSum (Finset.range N)
      (f := fun i b => ‖lam b i ^ ℓ - mu i ^ ℓ‖) (a := fun _ => (0 : ℝ))
      (fun i _ => by
        have h1 : Tendsto (fun b => lam b i ^ ℓ) atTop (𝓝 (mu i ^ ℓ)) := (hpt i).pow ℓ
        have h2 : Tendsto (fun b => lam b i ^ ℓ - mu i ^ ℓ) atTop (𝓝 0) := by
          simpa using h1.sub (tendsto_const_nhds (x := mu i ^ ℓ))
        simpa using h2.norm)
    simpa using h
  have hev1 : ∀ᶠ b in atTop,
      (∑ i ∈ Finset.range N, ‖lam b i ^ ℓ - mu i ^ ℓ‖) < ε / 2 :=
    hfin.eventually (gt_mem_nhds (by positivity))
  have hev2 : ∀ᶠ b in atTop, (∑' i, ‖lam b (i + N)‖ ^ ℓ) ≤ ε / 4 := by
    filter_upwards [hN₁] with b hb
    exact le_trans (tail_anti _ (hlamnn b) (hl b) (le_max_left _ _)) hb
  have hmuN : (∑' i, ‖mu (i + N)‖ ^ ℓ) ≤ ε / 4 :=
    le_trans (tail_anti _ hmunn hm (le_max_right _ _)) (le_of_lt hN₂)
  filter_upwards [hev1, hev2] with b h1 h2
  have hsplit : ‖F b - ∑' i, mu i ^ ℓ‖ ≤
      (∑ i ∈ Finset.range N, ‖lam b i ^ ℓ - mu i ^ ℓ‖)
        + (∑' i, ‖lam b (i + N)‖ ^ ℓ) + ∑' i, ‖mu (i + N)‖ ^ ℓ := by
    rw [hrepr b]
    exact v5_rank_split (lam b) mu ℓ N (hl b) hm
  linarith

end FriedEndpoints
