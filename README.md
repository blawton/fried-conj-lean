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
| `fried_crossing_rate_9_07` | crossing leg, companion (9/07): `hrate_nonclosed` DERIVED from the rank-2 cluster (memo main note §6 addendum; chronology 9/07) | `TwinRate.cluster_roots` (eigenvalues of M = s*·1 + τN are s* + τ·w with w² − (tr N)w + det N = 0 — exactly two, `branches_ne`), `twin_rate_of_cluster` (C¹ cluster data + a(0,0) = r₀ > 0 + b(0,0) = 0 ⇒ ∂_τ twin ≥ r₀/2 on a (θ,τ)-ball), `Crossing.crossing_exists_unique_local` (P3 with local control), `RateRatio.crossing_value_local` (hoff eventually), `Capstone.fried_fails_at_crossing_local`, `Capstone.fried_fails_at_crossing_of_cluster_inputs` (∃ θ₀ δ, ∀ 0 < |θ| < θ₀ …; σ ≤ 2|s*|/r₀) | zero axioms (hypothesis-shaped); `#print axioms` on all 9 theorems = built-ins only (audited 9/07). Ledger: hrate_nonclosed → (i) cluster-projector analyticity [sharpened risk (B)] + (ii) CDDP rate at θ = 0 + (iii) CDDP vanishing c-row; the rate now depends on hdouble (semisimplicity) BY TYPE. `fried_crossing_9_03` untouched — both capstones stand |
| `Basic.lean` | lake stub | — | — |

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
