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

## File map (`B1s/`, one file per leg — content stays in its leg's file)

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
| ⚡`fried_counterexample_main` | **THE STATEMENT FILE** (no date: it is the deliverable, not a leg). ONE theorem `fried_counterexample_of_inputs` whose hypothesis list IS the complete input ledger of the counterexample; proof = composition of the three crossing companion files; `#print axioms` at the bottom prints the certificate into every build log | see "The ledger" below | built-ins only (audited 9/08) |
| `Basic.lean` | lake stub | — | — |

## The ledger (`fried_counterexample_main.lean : fried_counterexample_of_inputs`)

ONE ROW PER BINDER, ONE BINDER PER MATHEMATICAL FACT. Facts with several technical components are
bundled as `structure`s (§1 of the file, namespace `Ledger`); their fields are listed in the "says"
column. Status: **[V]** verbatim in the cited paper · **[D]** derived in the vault memos from cited
facts · **[U]** not literally in any paper we hold (the open items) · **[def]** a definition or case
split, not a fact. Objects: M, M' = the 2×2 degree-1 cluster matrix and its τ-derivative; sStar =
s*(θ); B, p = CDDP's pairing on Res¹₀ and the (4.22) pairing of the non-closed state; a', b' =
τ-derivatives of tr N, det N (M − s*·1 = τN); e₁, e₂ = sum/product of the two pure degree-2
branches; z, R = the pure-zero branch and CD's regular factor; c, V_k = the zero cluster.

| binder | says | source | status |
|---|---|---|---|
| `hsemisimple` | M(θ,0) = s*(θ)·1 — the degree-1 cluster at g_hyp is the semisimple double point | `Saturation` (rate file §6): rank 2 [DGRS Prop 7.7 at θ=0 + bounded-twist rank constancy] + two independent states d₀f, I·d₀f [rederivation A2] | [D] |
| `hclusterC1` | `ClusterC1`: M entrywise C¹ in τ (`deriv`), ∂_τM jointly continuous at (0,0) (`cont`) | rank-2 half of input (B): CDDP Lemma 4.3 = continuity; one more derivative = standard resolvent perturbation; target citation Bonthonneau 1806.08125 | [U] |
| `h422` | `FirstVariation422`: det B ≠ 0 (`det_ne`); B·∂_τM(0,0) = !![0,0;0,p] (`eq422`), c-row/column vanish since dc = 0 | CDDP Lemma 2.2 + 2.10; CDDP (4.22) with (4.38) ι_Xβ = −b∘π | [V] |
| `hr₀` | r₀ := Bcc·p/det B > 0 | CDDP (1.3) non-degeneracy for b ∈ O (Thm 1(2)); sign = orientation of τ | [V] |
| `htraceDetC1` | `TraceDetC1`: tr N, det N C¹ in τ (`deriv_a`, `deriv_b`) with jointly continuous derivatives (`cont_a'`, `cont_b'`) | rank-2 half of (B), one derivative beyond `Hadamard` §2 (M C² in τ suffices) | [U] |
| `hdouble` | `DoublePoint`: s*(0) = 0 (`zero`), s* continuous at 0 (`cont`), s*(θ) < 0 for θ ≠ 0 (`neg`) | s* = −1+√(1−μ₀): DGRS (7.6) as meromorphic identity + BuOl Cor 5.1 (scalar Selberg zeros) + DFG Thm 2 cross-check; μ₀ = θ²‖ω‖²/vol + O(θ⁴) (Kato–Rellich) | [V] (BuOl via DGRS) |
| `hpureSumC2` | `PureSumC2`: K₁, ε > 0; e₁ C¹ in τ (`deriv_τ`), ∂_τe₁ C¹ in θ (`deriv_θτ`), mixed partial bounded by K₁ on the ε-square (`bound`) | **rank-4 half of (B) — the load-bearing uncited item**; C² of e₁ is all the counterexample needs | [U] |
| `hpureProdC3` | `PureProdC3`: K₂ > 0; e₂ C² in τ (`deriv_τ`, `deriv_ττ`), ∂²_τe₂ C¹ in θ (`deriv_θττ`), that derivative bounded by K₂ (`bound`) | rank-4 half of (B) | [U] |
| `hmirror_sum` | e₁(θ,0) = 0 — the two pure degree-2 zeros at g_hyp are at ±s*, so their sum vanishes | mirror (input A): DGRS (7.6) k = 2 factors Z_{S,σ₀}(λ) and Z_{S,σ₀}(λ+2) (dgrs 1876–1884) with BuOl scalar zeros | [V] (BuOl via DGRS) |
| `hmirror_prod` | e₂(θ,0) = −s*² — their product | same factors; the −s* state identified as f'·ω_s (rederivation A2, rate-ratio §2.1) | [D] |
| `hpinning` | `Pinning`: e₁(0,τ) = 0 (`sum`), e₂(0,τ) = 0 (`prod`) — at ρ_triv the pole leaves 0 alone, both pure zeros stay | pinning (input D): CDDP Cor 4.1 via Thm 1(2), m_{2,0}(0) = b₁+2 | [V] |
| `hτR` | τ_R(χ_θ) ≠ 0, Reidemeister torsion of the acyclic χ_θ | Fried 1986 at g_hyp | [V] |
| `hzQ` | z is a root of z² − e₁z + e₂ | quartic division `PureZeros.quartic_roots`, given the locked branches are roots (DGRS Lemma 7.1: d₀ commutes with L_X) | [D] |
| `hbranch` | at each crossing inside \|τ\| < δ, z is continuous with z = 0 — z is the pure-zero branch through 0 | definition of z | [def] |
| `hexactZero` | at each crossing e₂ = 0 — a pure degree-2 zero sits at 0 | exactness (input E): Dang–Rivière Thm 2.1 / DGRS (7.1); rederivation A6 | [V] |
| `hgeneric` | at each crossing e₁ ≠ 0 | generic case; the degenerate c₂ = 3 alternative is not in the Lean and also fails Fried | [def] |
| `hregular` | CD's regular factor F(0,·) continuous at the crossing | CD (6.5) + input (B) | [V] |
| `hfried_off` | off the crossing ζ(0; g_τ) = R·z/s_nc = τ_R | DGRS Thm 2 local constancy + Fried at g_hyp | [V] |
| `hexact` | the reduced complex C₀¹ → C₀² → C₀³ at the crossing is exact | Dang–Rivière Thm 2.1 / DGRS (7.1) | [V] |
| `hacyc` | c₀ = c₄ = 0 | DGRS Lemma 7.4 (+ ⋆) for acyclic unitary ρ | [V] |
| `hdual` | c₃ = c₁ | ⋆-duality, DGRS Lemma 7.2 | [V] |
| `hdims` | c_k = dim C₀^k for k = 1, 2, 3 | bookkeeping | [def] |

Conclusion: unique crossing σ ∈ (0, 2|s*|/r₀], ζ regular at 0, zero slope ∂_τe₂/e₁ with |·| > 2r₀
≥ pole slope, |e₁(θ,σ)| ≤ K₁|θ|σ, and ζ(0; g_σ) = τ_R·(pole rate)/(zero rate) ≠ τ_R with the Lemma A
torsion identity. ⚡Everything [U] is input (B); everything else is a citation to check.

⚡This table is hand-written. `python3 scripts/ledger_check.py` checks that every table row names
exactly one binder and that the set of binders in the statement theorem equals the set of rows — run
it after editing either.

Root `B1s.lean` imports every file; keep it current when adding files.
Import direction: `endpoints_8_20` imports `b1_spectral_skeleton_8_12` (never the
reverse — `tail_anti` is duplicated as `tail_anti'` for this reason).

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
