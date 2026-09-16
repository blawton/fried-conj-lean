# b1s — the Fried-program Lean suite

Machine-checked verification layer of the H ⇒ Fried program (vault:
`~/Downloads/fried_con/Fried Program/` — start at `Front Page.md` for the
mathematics, `program_chronology.md` for the dated arc). One Lake
project, one build, one audit surface. Lean 4 (`lean-toolchain` v4.33.0) + Mathlib.

## The method (read this first)

Analytic estimates and literature citations are NEVER proven here — Mathlib has no
hyperbolic dynamics, operator ideals, or manifold subellipticity. Instead every
theorem takes its citations as **named, citation-shaped hypotheses** (or, in
`b1_spectral` only, quarantined `axiom` vehicle constants), and everything
downstream is proved. The value is the LEDGER: `#print axioms <thm>` lists exactly
which mathematical inputs a result consumes; a scope mismatch at instantiation is a
type error, not a prose oversight. Each file's header states its own audit
criterion — re-run the audit after every change.

## How the pieces compose (⚡the capstone)

`fried_capstone_8_31.lean : fried_of_inputs` formally composes the suite: its
hypothesis list IS the program's input ledger, and `#print axioms` on it (built-ins
only) audits the whole chain at once. The wiring:

```
fried_of_inputs (T = zeta-side reading) ⟵ endpointGlue
  hconst  ⟵ BL Thm 6.7.1 [C]                      (constancy; M1 read DONE)
  h0      ⟵ BL Thm 8.2.1 [C]                      (b→0 torsion; residue: hbundle)
  hinf    ⟵ v5_limit_assembly_ofPointwise (endpoints §4) + hread [V2, flat trace]
    hpt     ⟵ Drouot Thm 5 [C, scalar, shape exact — read #3 DONE 9/01]
              + [W] bundle-valued appendix (vault drouot_read_3_9_01.md §4)
    htail   ⟵ hdom — THE one owed estimate (route: vault hdom_route_8_27)
    hl, hm  ⟵ trace-class bookkeeping [V1/V2-grade]
B1's own surface (b1_total_error_vanishes_ofPointwise) = the SAME (hpt, htail) pair.
Route-ii files: [uniform gap ⇒ endpoint strip]  — H's clause collapse.
h_mixing file : [endpoint mixing ⇒ uniform gap] — hmix = stage-1 × stage-2
                (Front Page ¶5; stage2_paper_program_8_31); future split
                hmix → hflow × htransfer.
```

So the entire program reduces, at audit grade, to: two citations to verify
(Drouot ✓ 9/01 → one appendix [W], V2), one estimate to prove (hdom), one photo (hbundle), and the
H-side sockets awaiting stage 1 (ours) and stage 2 (the unwritten paper).

## The three verified layers

1. **H ⇒ Fried** (the conditional reduction, the note's theorem) — five leg files,
   top-level glue `endpointGlue` in `endpoints_8_20.lean`.
2. **Route (ii)** (uniform gap ⇒ endpoint strip) — three grade files, 8/28.
3. **Stage 1 socket** (endpoint mixing ⇒ uniform gap, modulo `hmix`) —
   `h_mixing_equivalence_8_31.lean`. When stage 2 (twisted Dolgopyat) lands, it
   snaps in here and the chain closes by audit.

## File map (`B1s/`, one file per leg — content stays in its leg's file; ⚡since 9/14 the ONE exception is
`fried_statement_defs_9_14`, which holds every DEFINITION in the statement theorem's type, see "Palomar" below)

| file | leg / role | key results | audit expectation |
|---|---|---|---|
| `b1_spectral_skeleton_8_12` | B1 (trace control). ⚡The ONLY file with `axiom`s: the quarantined vehicle block V1–V5 + constants (b₀, θ, D, kineticRes, endpointRes, heatTrace, orbitSum) + the twisted variant's W-block | `b1_per_length`, `b1_aggregate` (window-free!), `b1_aggregate_twisted`, V5 tail spine (`v5_tail_le/tendsto/rank_split`), Weyl bridge (`hdom_of_weyl`, `hdom_pow_of_weyl`), window composition (`b1_total_error_vanishes`, zero-axiom `window_race`), V5-from-parts (`drift_of_parts`, `*_ofDrift`, `b1_total_error_vanishes_ofPointwise`) | `b1_aggregate`: exactly V1–V5 + vehicle. ⚡`b1_total_error_vanishes_ofPointwise`: V1–V4 only — NEITHER V5 NOR D (the placeholder is bypassed; inputs = `hpt` [Drouot] + `htail` [hdom]). `window_race`, `drift_of_parts`: zero axioms |
| `object_matching_s1_8_15` | object matching (S¹ model, T1–T4) | v1 identities | zero axioms |
| `bridge_8_20` | THE bridge (17 thms; supersedes 3 archived files) | two-channel MIN composition, gap-2 spine | zero axioms (hypothesis-shaped) |
| `endpoints_8_20` | endpoints + M1 interface + leg-5b assembly | `endpointGlue` (THE top-level theorem), `endpointGlueValue`, M1 typed checklist (`m1Consumption` — `hbundle` = sole remaining TO-FILL), `v5_limit_assembly`, `tail_anti`, `v5_limit_assembly_ofPointwise` | glue + assemblies: zero axioms |
| `route_ii_attainment_8_28` | route (ii), spectral-set grade | `endpointClause_ofAttainment` + compact-form variants; finiteness proven unused | zero axioms |
| `route_ii_resolvent_8_28` | route (ii), holomorphic grade | limit-holomorphy, no-pole bridge; Montel absent from Mathlib ⇒ loc-unif is the citation shape | zero axioms |
| `route_ii_correlation_8_28` | route (ii), quantitative grade + consistency | `c1_no_uniform_C_at_isometric_endpoint` (uniform C on L² is FALSE — b^K forced) + witness + `c2` interchange | zero axioms |
| `h_mixing_equivalence_8_31` | stage 1 (mixing ⇒ H) | `block_telescope`, `uniform_gap_of_block_mixing` (H's shape from `hburn` + `hmix`), geometric→exp pieces, ⚡Itô–Kawada mechanism PROVED (`midpoint_strict_contraction`, `opNorm_avg_lt_one`), `dissipation_identity` (route 5) | zero axioms |
| `fried_crossing_9_03` | Fried at a codimension-one CROSSING metric (memos fried_counterexample_rederivation_9_03 / crossing_rate_ratio_9_03 / jordan_cluster_torsion_9_03 / zero_cluster_torsion_9_02) — the ledger for ζ(0; g_σ) = τ_R·(pole rate / zero rate) ≠ τ_R | P1 `TorsionCore` (explicit-matrix CD Def 3.2 torsion: semisimple −1, Jordan −(1+λ)/λ, `jordan_torsion_eq_neg_ratio` = Lemma A shape), P2 `OrderCount.order_zero_of_exact` (exact C₀¹→C₀²→C₀³ + ⋆ ⇒ c₂ = 2c₁ ⇒ ζ-order 0), P3 `Crossing.crossing_exists_unique` (IVT + monotone), P4 `RateRatio.crossing_value` (R(σ) = τ_R·b/a), P5 `Capstone.fried_fails_at_crossing_of_inputs` (hdouble, hsym, hrate_nonclosed, hrate_zero, hcont, hfried_off, hexact, hacyc, hdual + bookkeeping hdims, hτR) | zero axioms (hypothesis-shaped); `#print axioms` on P1–P5 = built-ins only (audited 9/03) |
| `fried_crossing_rate_9_07` | crossing leg, companion (9/07): `hrate_nonclosed` DERIVED from the rank-2 cluster (memo main note §6 addendum; chronology 9/07) | `TwinRate.cluster_roots` (eigenvalues of M = s*·1 + τN are s* + τ·w with w² − (tr N)w + det N = 0 — exactly two, `branches_ne`), `twin_rate_of_cluster` (C¹ cluster data + a(0,0) = r₀ > 0 + b(0,0) = 0 ⇒ ∂_τ twin ≥ r₀/2 on a (θ,τ)-ball), `Crossing.crossing_exists_unique_local` (P3 with local control), `RateRatio.crossing_value_local` (hoff eventually), `Capstone.fried_fails_at_crossing_local`, `Capstone.fried_fails_at_crossing_of_cluster_inputs` (∃ θ₀ δ, ∀ 0 < |θ| < θ₀ …; σ ≤ 2|s*|/r₀); ⚡§6 (9/08) `Saturation.scalar_of_two_eigenvectors` / `eigenvalue_eq_of_saturated` / `semisimple_of_saturated` — rank-2 range + two independent states at s* ⇒ operator = s*·1 ⇒ NO third degree-1 resonance in the disc and semisimple (closes hdouble's uncited ν₁-factor gap by COUNTING: rank 2 = DGRS Prop 7.7 at θ=0 + bounded-twist rank constancy; two states = rederivation A2) | zero axioms (hypothesis-shaped); `#print axioms` on all 12 theorems = built-ins only (audited 9/07, 9/08). Ledger: hrate_nonclosed → (i) cluster-projector analyticity [sharpened risk (B)] + (ii) CDDP rate at θ = 0 + (iii) CDDP vanishing c-row; the rate now depends on hdouble (semisimplicity) BY TYPE. `fried_crossing_9_03` untouched — both capstones stand |
| `fried_crossing_firstvariation_9_08` | crossing leg, companion (9/08): the rate ledger bottomed out in CDDP's DISPLAYED equations | §1 `FirstVariation` — CDDP (4.22) as 2×2 algebra: pairing B, (4.22) matrix P = !![0,0;0,p] (c-row/column vanish, dc = 0), pairing-relative N = unique solution of B·N = P (`Nmat`, `Nmat_unique`), det N = 0, tr N = B_cc·p/det B (the main note's r₀), `charpoly_roots` (eigenvalues EXACTLY {0, B_cc p/det B}), block-diagonal (3.55)–(3.56) ⇒ p/B_ψψ, `trace_Nmat_ne_zero_iff` (r₀ ≠ 0 ⟺ p ≠ 0 = CDDP (1.3)), `wPlus/wMinus_of_firstVariation`; §2 `Hadamard` — `Ndiv` = (M − s*·1)/τ, `M_eq` (M = s*·1 + τN identically), `entry_slope_eq` (entrywise MVT), `continuousAt_Ndiv_entry/trace/det` (joint continuity at (0,0) from that of ∂_τM), `cluster_roots_M` (roots of char poly of the ACTUAL cluster matrix = s* + τw±); §3 `Capstone.fried_fails_at_crossing_of_cddp_inputs` (ha0/hb0 REPLACED by h0 + hderiv + hM' + B·∂_τM(0,0) = P + det B ≠ 0 + orientation) | zero axioms (hypothesis-shaped); `#print axioms` on all 12 audited theorems = built-ins only (9/08). Residual regularity hypothesis: a = tr N, b = det N differentiable in τ with jointly continuous derivatives (one derivative beyond §2) |
| `fried_crossing_purezeros_9_08` | crossing leg, companion (9/08 pm): `hrate_zero` DERIVED from the rank-4 cluster | §1 `PureZeros.quartic_div/rem_eq_zero/quartic_factor/quartic_roots` (char quartic of the rank-4 cluster ÷ (z−s_cl)(z−s_nc) = the pure quadratic z² − e₁z + e₂, e₁ = c₁ − s_cl − s_nc, e₂ = c₂ − s_cl s_nc − (s_cl+s_nc)e₁, explicit); §2 `abs_le_of_vanish_axes` (two-variable Hadamard: vanish on both axes + bounded ∂_θ∂_τ ⇒ ≤ K|θ||τ|), `abs_le_of_vanish_θ`; §3 `crossing_estimates` (|e₁(θ,σ)| ≤ K₁|θ|σ; |∂_τe₂(θ,σ)| ≥ r₀|s*|/4 via MVT on [0,σ] + O(|θ|) bound on ∂²_τe₂; zero slope |∂_τe₂/e₁| > 2r₀); §4 `hasDerivAt_zero_branch` (a continuous root of Q through 0 coincides near σ with w∓ and has slope ∂_τe₂/e₁); §5 `Capstone.fried_fails_at_crossing_local'` (LinearArrival form) + ⚡`fried_fails_at_crossing_of_pure_zero_inputs` (NO hrate_zero: inputs = e₁,e₂ joint regularity [rank-4 half of (B), bounded ∂_θ∂_τe₁ and ∂_θ∂²_τe₂], mirror A, pinning D, exactness E at crossings, generic e₁(σ) ≠ 0, z a continuous root through 0; conclusion adds slope = ∂_τe₂/e₁ > 2r₀ and the e₁ bound) | zero axioms (hypothesis-shaped); `#print axioms` on 8 audited theorems = built-ins only (9/08 pm). ⚡SHARPENING: C² (bounded mixed partial of e₁) suffices for the counterexample (κ = O(θ)); C³/evenness only give κ = O(θ²) |
| `fried_cluster_matrices_9_10` | crossing leg, companion (9/10): THE CLUSTER MATRICES AS PRIMITIVES — input (B) collapsed to ONE fact | §1 `ClusterMatrix` (charpoly of the 4×4 cluster = `PureZeros.quartic` with c_k its coefficients, `eval_charpoly_eq_quartic`; e₁ = c₁ − tr M, e₂ = c₂ − det M − (tr M)e₁ as `E₁`/`E₂` = the pure-zeros file's `e₁of`/`e₂of` when s_cl + s_nc = tr M, s_cl s_nc = det M; C^k of det / charpoly coefficients [Mathlib `charpoly_coeff_eq_sum_minors`] / trace in the entries) · §2 `Regularity` (`pτ`, `pθ` partials: jointly C^{m+1} ⇒ partial jointly C^m via `fderiv_right` + `clm_apply`; `bound_on_square`) · §3 `HQuot` (Hadamard quotient q = (f(τ)−f(0))/τ of a C² function is C¹: `taylor2` = Lagrange remainder from two MVTs, `hasDerivAt_hq` incl. q'(0) = f''(0)/2, `continuousAt_hq'` joint continuity in a parameter) · §4 `Ledger.ClusterC3` (joint C³ of the entries of M and A) ⇒ `Derived.clusterC1_of_C3`, `traceDetC1_of_C3` (a' = tr ∂_τN, b' by the product rule, N' = `hq'` entrywise), `pureSumC2_of_C3`, `pureProdC3_of_C3` (unit square, K from compactness); the four old bundles now live here as DERIVED targets · §5 `Spectral` (`coeffs_of_mirror`/`coeffs_of_pinned` by evaluation at z = 0, ±1, 2; `E₁_mirror`, `E₂_mirror`, `E₁_pinned`, `E₂_pinned`; `charpoly_factor_locked` = quartic division as a polynomial identity; ⚡`crossing_pure_data`: rootMultiplicity₀(charpoly A) = 2 ⇒ e₂ = 0 ∧ e₁ ≠ 0 — the former `hexactZero`/`hgeneric`) · §6 `Capstone.fried_fails_at_crossing_of_matrix_inputs` · ⚡§8 (9/14) `Derived.matrix_scalar_of_two_eigenvectors` / `semisimple_of_states` (hsemisimple from two independent states, via `Saturation`) · ⚡§7 (9/11) `Branch.zBranch` = the root of Q nearest 0, `zBranch_root` (a root wherever disc ≥ 0), `zBranch_at_simple_zero` (continuous and 0 where Q has the simple root 0) ⇒ z is DEFINED, `hzQ`/`hbranch` gone; `Ledger.ZetaFactorization` = CD (6.5) at λ = 0 (off/cont/at_crossing), capstone conclusion now about ζ₀(σ); `Derived.resZero₁/₂` + `finrank_resZero₁/₂` (Mathlib `finrank_maxGenEigenspace_eq` + `charpoly_toLin'`) make the Riesz dictionary a theorem | zero axioms (hypothesis-shaped); `#print axioms` on all audited theorems = built-ins only (9/10). ⚡Also 9/10: `fried_fails_at_crossing_of_pure_zero_inputs` now exports θ₀ ≤ ε ∧ δ ≤ ε (additive) so the dictionary derivation can use disc > 0 on the crossing range; 9/11: its `hzQ` and `hasDerivAt_zero_branch`'s are WEAKENED to "a root wherever disc ≥ 0" (what the proof used); `fried_fails_at_crossing_local_ord` and `fried_fails_at_crossing_of_pure_zero_inputs_ord` take `zetaOrder c = 0` at each crossing in place of the exactness quartet, the originals are corollaries |
| `resolvent_scale_9_11` | input (B), the operator-calculus shell (9/11 eve): a RESOLVENT FAMILY ON A BANACH SCALE IS C^k WITH LOSS | §1 `Scale.BanachScale` (ℕ-indexed real Banach spaces, coherent inclusions `incl a b`), `Scale.ResolventFamily` (fields = the cited facts: `bdd` local uniform boundedness [CDDP Lemma 4.3], `inv_left`/`inv_right` two-sided inverse modulo inclusion [Lemma 4.3], `smooth` generator C^∞ in the parameter, `R_incl`/`B_incl` compatibilities), `resolvent_identity` = CDDP (4.12) DERIVED from the inverse relations · §2 `R_incl_gen`/`B_incl_gen`, `locallyLipschitz_loss_one` (CDDP's "locally Lipschitz in τ"), `continuous_loss` · §3 `hasFDerivAt_loss` = CDDP (4.13): for a ≥ b+2 the family incl a b ∘ R a x is Fréchet differentiable with derivative `derivLoss` = −(incl∘R) ∘ ∂B ∘ (incl∘R); proof = (Lipschitz-with-loss)×O(h) + (bounded)×o(h) · §4 `lossBudget` (L 0 = 1, L (k+1) = 2L k + 1), `fderiv_B_incl_gen`, `derivSplit` + `derivSplit_apply_canonical` (all splits equal the level-b canonical derivative), `contDiff_derivSplit`, ⚡`contDiff_loss`: b + L k ≤ a ⇒ ContDiff ℝ k (incl a b ∘ R a ·) | zero axioms (hypothesis-shaped); `#print axioms` = built-ins only (9/11). No dynamics, no anisotropic spaces: pure Banach-space calculus |
| `cluster_from_resolvent_9_11` | input (B) DERIVED (9/11 eve): from the scale theorem to `Ledger.ClusterC3` | §1 `ParamInt.contDiff_parametric_intervalIntegral` (jointly C^n integrand on a compact interval ⇒ C^n parametric integral; induction with `hasFDerivAt_integral_of_dominated_of_fderiv_le`, bound by compactness — NOT in Mathlib) · §2 `ComplexStructure` (J, J² = −1, commutes with incl), `melem` = ⟨(incl∘R)φ, ℓ⟩_ℂ := ℓ(Tφ) − i·ℓ(J Tφ), `contDiff_melem` (C³ for loss ≥ 15) · §3 `contour`, `riesz` = −(1/2πi)∮ over a fixed circle as an interval integral, `contDiff_riesz` · §4 `FrameData` (φ_j at level a, real functionals ℓ_l at level b ≤ a − 15, contour), `Amat` = ⟨Π̃φ_j, ℓ_l⟩, `Bmat` = ⟨PΠ̃φ_j, ℓ_l⟩ via P R(λ) = incl + λR(λ), ⚡`Mframe` := A⁻¹B (the DEFINITION of the cluster matrix in the moving frame), `contDiff_det/adjugate/inv/mul_complex`, `contDiff_Mframe` (det A ≠ 0) · §5 `Mreal` = real part, `contDiff_Mreal`, ⚡`clusterC3_of_resolvent` | zero axioms (hypothesis-shaped); built-ins only (9/11). Reality of the cluster matrices (Im = 0) is interpretive, not consumed |
| ⚡`fried_counterexample_main` | **THE STATEMENT FILE** (no date: it is the deliverable, not a leg). `fried_counterexample_of_inputs` (§2: the cluster matrices M, A as primitives, `hclusterC3` a hypothesis) and ⚡⚡`fried_counterexample_of_resolvent_inputs` (§3, 9/11 eve: M := `Mreal F₁ J₁ D₁`, A := `Mreal F₂ J₂ D₂` DEFINED from two resolvent families; `hclusterC3` DISCHARGED by `clusterC3_of_resolvent`; NO uncited row); both print `#print axioms` certificates into every build log | see "The ledger" below | built-ins only (audited 9/11) |
| ⚡`fried_statement_defs_9_14` | THE STATEMENT'S DEFINITIONS, one module, fixed order (9/14, Palomar): TorsionCore (d₁–d₃, D-mats, N_C, m_C, `refinedTorsion`), `zetaOrder`, TwinRate (`disc`, `wPlus/wMinus`, `twin`, `dwPlus`, `dtwin`), FirstVariation (`Bmat`, `Pmat`), `Hadamard.Ndiv`, ClusterMatrix (c₁–c₄, E₁, E₂), Regularity (`pτ`, `pθ`), HQuot (`hq`, `hq'`), Ledger (`Pinned`, `ZetaFactorization`, `FirstVariation422`, `DoublePoint`), Derived (`Mτ`, `Mττ`, `Nτ`, `aτ`, `bτ`, `E₁f`, `E₂f`, `resZero₁/₂`), `Branch.zBranch`, Scale (`BanachScale`, `ResolventFamily`), ClusterFrame (`Param`, `ComplexStructure`, `melem`, `contour`, `riesz`, `FrameData`, `Amat`, `Bmat`, `Mframe`, `Mreal`) — imported by `fried_crossing_9_03` and `resolvent_scale_9_11`, so by the whole crossing chain | definitions only, no theorems | ⚡ORDER IS LOAD-BEARING (comparator aux-proof cache, see Palomar section): append, never reorder; regenerate `Challenge.lean` after any edit |
| `Basic.lean` | lake stub | — | — |

## The ledger (`fried_counterexample_main.lean : fried_counterexample_of_resolvent_inputs`)

ONE ROW PER BINDER, ONE BINDER PER MATHEMATICAL FACT (⚡⚡9/11 eve: `hclusterC3` is GONE — input (B) is a THEOREM from the resolvent data, see the second table; 16 binders, [U] = 0. ⚡9/14: `hsemisimple` → `hstates`, count unchanged. ⚡9/10: 18 binders, was 22; ⚡9/11: 16 — the pure-zero branch z is DEFINED as `Branch.zBranch`, the root of Q nearest 0; then 15 — C₀¹, C₀² DEFINED as the generalized 0-eigenspaces of the cluster matrices (`Derived.resZero₁/₂`), dimensions = multiplicities by Mathlib `LinearMap.finrank_maxGenEigenspace_eq`, so `hriesz` is gone; C₀³ = abstract V₃; [U] 4 → 1). Facts with
several technical components are bundled as `structure`s (`Ledger` namespace: `ClusterC3`, `Pinned` in the 9/10
leg file; `FirstVariation422`, `DoublePoint` in the statement file); their fields are listed in the "says"
column. Status: **[V]** verbatim in the cited paper · **[D]** derived in the vault memos from cited facts ·
**[U]** not literally in any paper we hold (the open items) · **[def]** a definition or case split, not a fact.
Objects (9/11 eve): S₁, S₂ = the anisotropic scales in degrees 1 and 2 (`Scale.BanachScale`); F₁, F₂ = the resolvent families of the twisted deformed generator on them (`Scale.ResolventFamily`, fields = cited facts, second table); J₁, J₂ = complex structures; D₁, D₂ = frames (φ_j, ℓ_l, contour); M := `Mreal F₁ J₁ D₁`, A := `Mreal F₂ J₂ D₂` = the 2×2 degree-1 and 4×4 degree-2 cluster matrices at (θ,τ), DEFINED as real parts of the frame matrices A(p)⁻¹B(p); sStar = s*(θ); B, p = CDDP's
pairing on Res¹₀ and the (4.22) pairing of the non-closed state; z, F = the pure-zero branch and CD's regular
factor (⚡9/11: the ζ-side objects are ζ₀ = τ ↦ ζ(0; g_τ) and F, the conclusion is about ζ₀(σ)); c, V_k = the zero cluster. ⚡DEFINED, not hypothesised (9/10 leg file): z = `Branch.zBranch (e₁ θ) (e₂ θ)` (9/11); ∂_τM = `Derived.Mτ M`;
N = `Hadamard.Ndiv M (Mτ M) sStar`; a = tr N, b = det N, a' = `Derived.aτ M`, b' = `Derived.bτ M sStar`;
e₁ = c₁(A) − tr M, e₂ = c₂(A) − det M − (tr M)e₁ (`Derived.E₁f`, `E₂f`); e₂τ = `Regularity.pτ e₂`.

| binder | says | source | status |
|---|---|---|---|
| `hstates` | for every θ, two linearly independent vectors v₁, v₂ with M(θ,0)v_i = s*(θ)v_i — the resonant states d₀f and I·d₀f at the double point; the cluster's rank 2 is the TYPE Fin 2 (⇒ M(θ,0) = s*·1 by `Derived.semisimple_of_states` = `Saturation` §6 through `Matrix.toLin'`; the former `hsemisimple` [D] is now derived) | d₀f := df + s*fα resonant at s* from the degree-0 state (DGRS (7.6), rederivation A2); I·d₀f resonant since I commutes with the flow (CDDP (3.7), cddp 1877–1883, 2662); independence = Liouville on S² (A2) [D]; rank 2 = DGRS Prop 7.7 m₁(0) = 2b₁ + bounded-twist rank constancy [V] | [D] (independence) |
| `hdet₁` | det A₁(p) ≠ 0 for all p: the degree-1 frame Π̃(p)φ_j is nondegenerate against the dual functionals ℓ_l | choice of frame: dual frame at (0,0) (CP20 §6.2), parameters retracted into the region where it stays invertible | [def] |
| `hdet₂` | det A₂(p) ≠ 0 for all p: the degree-2 frame | same | [def] |
| `h422` | `FirstVariation422`: det B ≠ 0 (`det_ne`); B·∂_τM(0,0) = !![0,0;0,p] (`eq422`) with ∂_τM = `Mτ M` | CDDP Lemma 2.2 + 2.10; CDDP (4.22) with (4.38) ι_Xβ = −b∘π | [V] |
| `hr₀` | r₀ := Bcc·p/det B > 0 | CDDP (1.3) non-degeneracy for b ∈ O (Thm 1(2)); sign = orientation of τ | [V] |
| `hdouble` | `DoublePoint`: s*(0) = 0 (`zero`), s* continuous at 0 (`cont`), s*(θ) < 0 for θ ≠ 0 (`neg`) | s* = −1+√(1−μ₀): DGRS (7.6) as meromorphic identity + BuOl Cor 5.1 (scalar Selberg zeros) + DFG Thm 2 cross-check; μ₀ = θ²‖ω‖²/vol + O(θ⁴) (Kato–Rellich) | [V] (BuOl via DGRS) |
| `hmirror` | charpoly A(θ,0) = (z − s*)³(z + s*): the degree-2 cluster at g_hyp is the locked pair at s* plus the pure pair at ±s* (⇒ e₁(θ,0) = 0, e₂(θ,0) = −s*², `Spectral.E₁_mirror`/`E₂_mirror`) | mirror (input A): DGRS (7.6) k = 2 factors Z_{S,σ₀}(λ) and Z_{S,σ₀}(λ+2) (dgrs 1876–1884) with BuOl scalar zeros [V]; the −s* state identified as f'·ω_s (rederivation A2, rate-ratio §2.1) [D]; ⚡replaces `hmirror_sum` + `hmirror_prod` | [V]+[D] |
| `hpinning` | `Pinned`: det M(0,τ) = 0 (`deg1`); charpoly A(0,τ) = z³(z − tr M(0,τ)) (`deg2`) — at ρ_triv the degree-2 cluster is {0,0,0,twin} (⇒ e₁(0,τ) = e₂(0,τ) = 0, `Spectral.E₁_pinned`/`E₂_pinned`) | pinning (input D): CDDP Cor 4.1 via Thm 1(2), m_{2,0}(0) = b₁+2 = 3; the fourth eigenvalue = the lifted twin d₀u_nc (DGRS Lemma 7.1); deg1 = the harmonic 1-form (b₁ = 1) | [V] |
| `hlocked` | every eigenvalue of M(θ,τ) is an eigenvalue of A(θ,τ) — the locked branches (⇒ charpoly A = (X−s_cl)(X−s_nc)·Q, `Spectral.charpoly_factor_locked`) | DGRS Lemma 7.1 (d₀ commutes with L_X: lifts the twin); ∧dα lifts the closed branch (f·dα = d₀²f/s_cl) | [V] |
| `hτR` | τ_R(χ_θ) ≠ 0, Reidemeister torsion of the acyclic χ_θ | Fried 1986 at g_hyp | [V] |
| `hfactor` | `ZetaFactorization`: with ζ₀(τ) = ζ(0; g_τ) and F the regular factor — ζ₀ = F·z/s_nc off the crossing (`off`), F continuous at the crossing (`cont`), ζ₀(σ) = F(σ) at the crossing (`at_crossing`, the cluster factor is λ/λ) | Chaubet–Dang (6.5) read at λ = 0 along the conformal family; continuity of F in τ = input (B)-type regularity. ⚡9/11: replaces `hregular` + the R·z/s shape of the old `hfried_off` | [V] |
| `hfried_off` | off the crossing ζ₀(τ) = ζ(0; g_τ) = τ_R | DGRS Thm 2 local constancy of ζ(0) in the vector field + Fried at g_hyp | [V] |
| `hexact` | at each crossing inside \|τ\| < δ the reduced complex C₀¹ → C₀² → C₀³ is exact, with C₀¹ = `resZero₁ M θ σ`, C₀² = `resZero₂ A θ σ` (generalized 0-eigenspaces of the cluster matrices) and C₀³ = the abstract V₃ (⚡yields e₂(θ,σ) = 0 and e₁(θ,σ) ≠ 0 — the former `hexactZero` [V] and `hgeneric` [def] — via `Spectral.crossing_pure_data`, and the ζ-order 0) | Dang–Rivière Thm 2.1 / DGRS (7.1) | [V] |
| `hacyc` | c₀ = c₄ = 0 | DGRS Lemma 7.4 (+ ⋆) for acyclic unitary ρ | [V] |
| `hdual` | c₃ = c₁ | ⋆-duality, DGRS Lemma 7.2 | [V] |
| `hdims` | c_k = dim C₀^k for k = 1, 2, 3 at each crossing inside \|τ\| < δ (k = 1, 2: dimensions of `resZero₁/₂`, = algebraic multiplicities of 0 by Mathlib; k = 3: dim V₃) | bookkeeping | [def] |

**The analytic inputs inside F₁, F₂ (`Scale.ResolventFamily`, one row per field; the former `hclusterC3` [U]):**

| field | says | source | status |
|---|---|---|---|
| `bdd` | ‖R n x‖ bounded locally uniformly in the parameter x = (θ,τ,λ), on every level n | CDDP Lemma 4.3 (cddp.txt 3632–3645): "the resolvent is bounded locally uniformly in τ, λ outside" the (closed) resonance set; θ affine bounded twist | [V] |
| `inv_left`, `inv_right` | R n x is a two-sided inverse of the generator B n x = P(θ,τ) − λ modulo the inclusion, on every level | CDDP Lemma 4.3: Fredholm with inverse R(λ) on H^{r,s} for r > C₀ + \|s\| | [V] |
| `smooth` | x ↦ B n x is C^∞ into L(H (n+1), H n) | affine in θ (bounded twist iθ·ω(X)) and λ; smooth in τ (L_{X_τ} for the conformal family) | [V]-grade standard |
| `R_incl`, `B_incl` | resolvent and generator commute with the inclusions of the scale | the scale is one operator on nested spaces | [def] |
| `J`, `J_sq`, `J_incl` (`ComplexStructure`) | multiplication by i on each level | the spaces are complex | [def] |
| retraction | the families are pulled back by smooth retractions of (θ,τ) into the neighbourhood of (0,0) and of λ into an annulus around the contour where the resolvent exists | CDDP §4.2 fixed resonance-free contour; standard | [def] |

⚡Consequence: `#print axioms fried_counterexample_of_resolvent_inputs` = built-ins, and every hypothesis is either
verbatim in a paper we hold, derived in a vault memo, or a definition. ⚡9/14: `hsemisimple` replaced by its input `hstates` (two independent states at s*); the only [D] left is the Liouville independence of d₀f and I·d₀f inside `hstates`.

Conclusion: ∃ K₁ > 0 (from compactness) and θ₀, δ > 0 such that for 0 < |θ| < θ₀: unique crossing
σ ∈ (0, 2|s*|/r₀], ζ regular at 0, zero slope ∂_τe₂/e₁ with |·| > 2r₀ ≥ pole slope, |e₁(θ,σ)| ≤ K₁|θ|σ, and
ζ₀(σ) = ζ(0; g_σ) = τ_R·(pole rate)/(zero rate) ≠ τ_R with the Lemma A torsion identity. ⚡No [U] remains (9/11 eve).

⚡This table is hand-written. `python3 scripts/ledger_check.py` checks that every table row names
exactly one binder and that the set of binders in the statement theorem equals the set of rows — run
it after editing either.

Root `B1s.lean` imports every file; keep it current when adding files.
Import chain of the crossing leg: `fried_statement_defs_9_14` ← `fried_crossing_9_03` ← `_rate_9_07` ← `_firstvariation_9_08` ←
`_purezeros_9_08` ← `fried_cluster_matrices_9_10` ← `cluster_from_resolvent_9_11` (which also imports
`resolvent_scale_9_11`, and `resolvent_scale_9_11` imports `fried_statement_defs_9_14`) ← `fried_counterexample_main`.
Import direction: `endpoints_8_20` imports `b1_spectral_skeleton_8_12` (never the
reverse — `tail_anti` is duplicated as `tail_anti'` for this reason).

## Palomar submission surface (9/14)

Palomar (https://palomar-registry.org) registers one public GitHub commit per result and checks it with
`leanprover/comparator`. The surface lives at the repo root and is REGENERATED, not hand-edited:

| file | role |
|---|---|
| `Challenge.lean` | the statement of record: imports ONLY Mathlib; = `B1s/fried_statement_defs_9_14.lean` verbatim + `fried_counterexample_of_resolvent_inputs` with `sorry`. ⚡GENERATED by `python3 scripts/make_challenge.py` (`--check` in CI/audit) |
| `Solution.lean` | `import B1s.fried_counterexample_main` — the development, re-exported; the development never imports `Challenge` |
| `comparator.json` | the one compared theorem, the three standard axioms, `enable_nanoda: true` (Palomar's CI supplies NanoDa) |
| `formalization.yaml` | v0.4 metadata (project name DECIDED 9/15: "Resonance-cluster analysis for a proposed counterexample to Fried's conjecture"): branch paragraph → six groups of cited facts → "geometric identification not formalized"; `automation.methods` names the model; authors = humans only |
| `LICENSE` | Apache-2.0 (DECIDED 9/16), verbatim text from apache.org |
| `docs/counterexample_intuitive_view.tex/.pdf` | the figures companion to the informal account (six TikZ figures: the two dials, the twin, unequal arrival speeds, the jump), revised 9/15 from the vault original: vault-internal framing removed, Status = the agreed caveat (conditional reduction, cited inputs, not yet verified by a mathematician other than the author), aligned with the six groups and the branch vocabulary, AI-assistance line added; ⚡9/15 pm new §2 "The argument in one page" (signs/counts c_k, exactness ⇒ order 0 via c₂ = 2c₁, who supplies the second degree-2 state ⇒ e₂ = 0 ≠ e₁, the value as a limit of the continuous factor F) |

⚡WHY the definitions live in ONE module: comparator compares definitions BY VALUE. A real numeral in a
definition body (`/ 2`, `4 * b`, `2 * π`) makes Lean lift the `Nat.AtLeastTwo` instance proof into a hidden
auxiliary lemma named after the FIRST definition in the current module that needed it, cached per module.
Spread over seven files, `hq'` owned its own copy in the development but reused `wPlus`'s in the one-file
Challenge ⇒ `Const does not match … HQuot.hq'` (seen 9/14). Same module + same order on both sides ⇒ same
cache ⇒ match. Hence: every statement definition in `fried_statement_defs_9_14`, appended in order, never
reordered, and `Challenge.lean` generated from it.

Local run (comparator built from its `v4.33.0` tag; on macOS the Linux sandbox is faked):
```
COMPARATOR_LANDRUN=<comparator>/scripts/fake-landrun.sh \
COMPARATOR_LEAN4EXPORT=<comparator>/.lake/packages/lean4export/.lake/build/bin/lean4export \
lake env <comparator>/.lake/build/bin/comparator comparator.json      # set enable_nanoda false locally
```
Negative controls to rerun after any change: weaken one Challenge hypothesis ⇒ statement mismatch; add a
theorem using a custom axiom to `theorem_names` ⇒ illegal axiom.

## Build & audit

```
cd ~/Downloads/fried_con/b1s
lake build                                  # full suite (~3-5 min incremental)
lake env lean B1s/<file>.lean               # elaborate ONE file (no build-dir writes;
                                            #   safe for concurrent agents — NEVER run
                                            #   parallel `lake build`s)
# audit: write a scratch file with `import B1s.<file>` + `#print axioms <thm>`,
# then `lake env lean <scratch>` (see vault chronology 8/28-8/31 for examples)
```

## House rules

- **Zero sorries in deliverables.** Phase-1 sorry-statements only during design.
- **Grep Mathlib for names, never guess**: `grep -rn "theorem <name>" .lake/packages/mathlib/Mathlib/...`
- **Default heartbeat budget only** (no `set_option maxHeartbeats`): split
  declarations or name opaque constants instead (see 8/31 refactor of
  `b1_total_error_vanishes_ofPointwise` — proof works against an opaque `C`, with
  `finite_drift_tendsto` and `b1_eps_step` factored out).
- **Scripted edits: `cp file file.bak` first + assert marker uniqueness**
  (`s.count(marker) == 1`). ⚡Under git since 9/02 (`git init` by Ben; Ben runs ALL git — agents only edit
  files and never commit). Keep `.bak*` out of the tree (gitignored); commit after each
  green build.
- Dates in filenames are creation dates; content is appended in sections with dated
  headers (`/-! ## ... (8/28 ...) -/`), matching the vault convention.
