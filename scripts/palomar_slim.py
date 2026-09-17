#!/usr/bin/env python3
"""Slim the repository to the Palomar entry (9/16).

Removes the earlier H ⇒ Fried programme (ten Lean files + archive/), rewrites the root import list,
replaces README.md with the public-facing document, and trims the scope paragraph of formalization.yaml.
Idempotent: safe to rerun. Run from the repository root:

    python3 scripts/palomar_slim.py
    python3 scripts/make_challenge.py --check && python3 scripts/ledger_check.py
    lake build            # optional here; Palomar's CI builds Challenge and Solution itself
"""
import pathlib, shutil, sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
B1S = ROOT / "B1s"

PROGRAMME_FILES = [
    "b1_spectral_skeleton_8_12", "object_matching_s1_8_15", "bridge_8_20", "endpoints_8_20",
    "route_ii_attainment_8_28", "route_ii_resolvent_8_28", "route_ii_correlation_8_28",
    "h_mixing_equivalence_8_31", "fried_capstone_8_31",
]
CROSSING_FILES = [
    "fried_statement_defs_9_14", "fried_crossing_9_03", "fried_crossing_rate_9_07",
    "fried_crossing_firstvariation_9_08", "fried_crossing_purezeros_9_08", "fried_cluster_matrices_9_10",
    "resolvent_scale_9_11", "cluster_from_resolvent_9_11", "fried_counterexample_main",
]

def remove_programme():
    for f in PROGRAMME_FILES:
        p = B1S / f"{f}.lean"
        if p.exists():
            p.unlink(); print("removed", p.relative_to(ROOT))
    arch = ROOT / "archive"
    if arch.exists():
        shutil.rmtree(arch); print("removed archive/")
    for stale in ["README.md.bak_9_10", "scripts/audit_9_10.lean"]:
        p = ROOT / stale
        if p.exists():
            p.unlink(); print("removed", stale)

def write_root_imports():
    lines = ["import B1s.Basic"] + [f"import B1s.{f}" for f in CROSSING_FILES]
    (ROOT / "B1s.lean").write_text("\n".join(lines) + "\n"); print("wrote B1s.lean")

def trim_yaml_scope():
    p = ROOT / "formalization.yaml"; s = p.read_text()
    old = """ The repository
    also contains an earlier form of the same theorem, fried_counterexample_of_inputs, in which the joint
    C³ regularity of the cluster matrices is a hypothesis rather than derived from the resolvent
    families; it is not compared. The repository's other files (b1_spectral_skeleton_8_12, bridge_8_20,
    endpoints_8_20, the route_ii files, h_mixing_equivalence_8_31, fried_capstone_8_31,
    object_matching_s1_8_15) belong to a separate conditional programme (a uniform twisted kinetic gap
    ⇒ Fried) and are not part of this submission; b1_spectral_skeleton_8_12 declares quarantined
    `axiom`s, none of which is reachable from the compared declaration or from any file in its import
    chain."""
    new = """ The repository
    also contains an earlier form of the same theorem, fried_counterexample_of_inputs, in which the joint
    C³ regularity of the cluster matrices is a hypothesis rather than derived from the resolvent
    families; it is not compared. No file in the repository declares an axiom."""
    if old in s:
        s = s.replace(old, new)
    old2 = """  - >-
    The repository proves more than is compared (the uncompared fried_counterexample_of_inputs, the
    per-leg theorems, and the separate kinetic-gap programme in the other files). One file of that
    programme, b1_spectral_skeleton_8_12, declares quarantined axioms; nothing compared reaches them."""
    new2 = """  - >-
    The repository proves more than is compared: the uncompared fried_counterexample_of_inputs and the
    per-leg theorems it rests on. No file declares an axiom."""
    if old2 in s:
        s = s.replace(old2, new2)
    p.write_text(s); print("trimmed formalization.yaml scope")

README = r'''# Resonance-cluster analysis for a proposed counterexample to Fried's conjecture

Lean 4 / Mathlib formalization of one theorem, `FriedCrossing.fried_counterexample_of_resolvent_inputs`:
the machine-checked reduction behind a proposed codimension-one failure of Fried's identity
ζ(0) = τ_R for acyclic characters on a closed hyperbolic 3-manifold with b₁ = 1. Registered-entry
surface for [Palomar](https://palomar-registry.org); Lean `v4.33.0`, Mathlib pinned in `lake-manifest.json`.

## The theorem in words

Near (g_hyp, ρ_triv), along the conformal family g_τ = e^{−2τb} g_hyp with characters χ_θ, the Ruelle
resonances near 0 form two small clusters: a rank-2 cluster in degree 1, encoded by a 2×2 matrix
M(θ,τ), and a rank-4 cluster in degree 2, encoded by a 4×4 matrix A(θ,τ). A *branch* is one eigenvalue
of a cluster matrix followed continuously in (θ,τ). Degree 1 has the closed branch and the *twin*
s_nc(θ,τ), which starts at the double point s*(θ) < 0 and travels at rate r₀ > 0 towards 0. Degree 2 has
the two locked branches (the same eigenvalues, lifted by d₀) and two pure branches, the roots of
Q = X² − e₁X + e₂; the pure branch nearest 0 is z(θ,τ). At the crossing metric τ = σ(θ) the twin and z
reach 0 together, the twin as a pole of ζ and z as a zero, so ζ stays regular at 0 and

  ζ(0; g_σ) = τ_R · (rate of the twin)/(rate of z).

The twin's rate is at most 2r₀ and z's exceeds 2r₀, so ζ(0; g_σ) ≠ τ_R. Fried's identity would need the
two branches to arrive at the same speed. The whole Lean argument is bookkeeping of these four branches.

**What is proved.** A conditional reduction. The objects are two abstract resolvent families on Banach
scales (structure fields = the cited facts, CDDP Lemma 4.3), complex structures and nondegenerate frames;
M and A are *defined* from them as real parts of the frame matrices A(p)⁻¹B(p) built from contour
integrals of matrix elements of the resolvent. The sixteen hypotheses are the properties of that data the
argument uses, each cited to the literature (table below).

**Dependencies:** The identification of the abstract data with the geometry — that the resolvent families
are those of the twisted deformed generator on the anisotropic spaces of g_τ, that ζ₀(τ) is the Ruelle
zeta function of g_τ at 0, that τ_R is the Reidemeister torsion of χ_θ, and that the defined matrices are
the cluster matrices — is not formalized. Nothing about manifolds, flows, anisotropic spaces or zeta
functions is in Lean. The claim has not been verified by a mathematician other than the author.

Pictures and a one-page version of the argument: `docs/counterexample_intuitive_view.pdf`.

## Verify it

```
lake exe cache get            # Mathlib oleans (first time only)
lake build                    # whole suite; the build log prints `#print axioms` for the statement:
                              #   [propext, Classical.choice, Quot.sound]
python3 scripts/make_challenge.py --check   # Challenge.lean is generated, never hand-edited
python3 scripts/ledger_check.py             # README ledger rows ⟷ theorem binders, one-to-one
```

Comparator (what Palomar runs): `comparator.json` names the one theorem and the three standard axioms.
Locally, with `leanprover/comparator` built from its `v4.33.0` tag (on macOS the Linux sandbox is faked):

```
COMPARATOR_LANDRUN=<comparator>/scripts/fake-landrun.sh \
COMPARATOR_LEAN4EXPORT=<comparator>/.lake/packages/lean4export/.lake/build/bin/lean4export \
lake env <comparator>/.lake/build/bin/comparator comparator.json      # set enable_nanoda false locally
```

## Layout

| file | role |
|---|---|
| `Challenge.lean` | statement of record: imports only Mathlib; = `B1s/fried_statement_defs_9_14.lean` verbatim + the theorem with `sorry`. **Generated** by `scripts/make_challenge.py` |
| `Solution.lean` | `import B1s.fried_counterexample_main`: the development, re-exported. The development never imports `Challenge` |
| `comparator.json` | compared theorem, permitted axioms, NanoDa on |
| `formalization.yaml` | Palomar v0.4 metadata: abstract, sources, automation disclosure, fidelity notes |
| `docs/` | `counterexample_intuitive_view.tex/.pdf`, the figures companion |
| `B1s/fried_statement_defs_9_14.lean` | **every definition in the statement's type, one module, fixed order** (see "Why one module") |
| `B1s/fried_crossing_9_03.lean` | torsion of the zero cluster (Chaubet–Dang Def 3.2 as explicit matrices), order count (exact complex ⇒ c₂ = 2c₁ ⇒ ζ-order 0), crossing existence and uniqueness, rate-ratio value formula |
| `B1s/fried_crossing_rate_9_07.lean` | the twin's rate from the rank-2 cluster; `Saturation`: two independent states at s* ⇒ M(θ,0) = s*·1 |
| `B1s/fried_crossing_firstvariation_9_08.lean` | CDDP (4.22) as 2×2 algebra (r₀ = B_cc p/det B), the Hadamard quotient N = (M − s*·1)/τ |
| `B1s/fried_crossing_purezeros_9_08.lean` | the pure quadratic Q from the rank-4 cluster; two-variable Hadamard bound |e₁(θ,σ)| ≤ K₁|θ|σ; the zero's slope ∂_τe₂/e₁ > 2r₀ |
| `B1s/fried_cluster_matrices_9_10.lean` | the cluster matrices as primitives: e₁, e₂ from charpoly coefficients; mirror/pinning as spectra of A; `crossing_pure_data` (root multiplicity 2 at 0 ⇒ e₂ = 0, e₁ ≠ 0); `zBranch`; generalized 0-eigenspaces `resZero₁/₂` with dimensions = multiplicities (Mathlib) |
| `B1s/resolvent_scale_9_11.lean` | a resolvent family on a Banach scale is C^k with loss (CDDP (4.12)–(4.13) iterated); pure Banach-space calculus |
| `B1s/cluster_from_resolvent_9_11.lean` | C^n parametric interval integrals (not in Mathlib); contour integrals of matrix elements; frame matrices A⁻¹B; `clusterC3_of_resolvent` |
| `B1s/fried_counterexample_main.lean` | the statement file: `fried_counterexample_of_inputs` (C³ of the cluster matrices as a hypothesis) and `fried_counterexample_of_resolvent_inputs` (the compared theorem; C³ derived) |

Import chain: `fried_statement_defs_9_14` ← `fried_crossing_9_03` ← `_rate_9_07` ← `_firstvariation_9_08`
← `_purezeros_9_08` ← `fried_cluster_matrices_9_10` ← `cluster_from_resolvent_9_11` (also imports
`resolvent_scale_9_11` ← `fried_statement_defs_9_14`) ← `fried_counterexample_main`. Every theorem in
every file depends only on `propext`, `Classical.choice`, `Quot.sound`; no file declares an axiom.

### Why one module for the definitions

`comparator` compares definitions **by value**. A real numeral in a definition body (`/ 2`, `4 * b`, `2 * π`)
makes Lean lift the `Nat.AtLeastTwo` instance proof into a hidden auxiliary lemma named after the first
definition in the current module that needed it, cached per module. With the definitions spread over
several files, `hq'` owned its own copy in the development but reused `wPlus`'s in the single-file
Challenge, and comparator rejected the pair. Same module and same order on both sides ⇒ same cache ⇒
match. Hence: every statement definition in `fried_statement_defs_9_14`, appended in order, never
reordered, and `Challenge.lean` generated from it.

## The ledger: one row per binder, one binder per cited fact

Status: **[V]** verbatim in the cited paper · **[D]** derived in the accompanying note from cited facts ·
**[def]** a definition or a choice, not a fact. Sources: CDDP = Cekić–Delarue–Dyatlov–Paternain
(arXiv:2009.08558), DGRS = Dang–Guillarmou–Rivière–Shen (arXiv:1807.01189), BuOl = Bunke–Olbrich (1995),
DFG = Dyatlov–Faure–Guillarmou (arXiv:1403.0256), CD = Chaubet–Dang (arXiv:1911.09931),
DR = Dang–Rivière (arXiv:1703.08037), Fried 1986.

Objects: S₁, S₂ = Banach scales in degrees 1 and 2 (`Scale.BanachScale`); F₁, F₂ = resolvent families on
them (`Scale.ResolventFamily`, fields = cited facts, second table); J₁, J₂ = complex structures; D₁, D₂ =
frames; M := `Mreal F₁ J₁ D₁`, A := `Mreal F₂ J₂ D₂`; sStar = s*(θ); B, p = CDDP's pairing on Res¹₀ and
the (4.22) pairing of the non-closed state; ζ₀ = τ ↦ ζ(0; g_τ), F = CD's regular factor; c, V₃ = the zero
cluster's dimensions and abstract degree-3 space. Defined, not hypothesised: z = `Branch.zBranch`,
∂_τM = `Derived.Mτ`, N = `Hadamard.Ndiv`, a = tr N, b = det N, a' = `Derived.aτ`, b' = `Derived.bτ`,
e₁ = `Derived.E₁f`, e₂ = `Derived.E₂f`, e₂τ = `Regularity.pτ e₂`, C₀¹ = `resZero₁`, C₀² = `resZero₂`.

| binder | says | source | status |
|---|---|---|---|
| `hstates` | for every θ, two linearly independent vectors v₁, v₂ with M(θ,0)v_i = s*(θ)v_i — the resonant states d₀f and I·d₀f at the double point; rank 2 is the type Fin 2 (⇒ M(θ,0) = s*·1 by `Derived.semisimple_of_states`) | d₀f resonant at s* from the degree-0 state (DGRS (7.6)); I·d₀f resonant since I commutes with the flow (CDDP (3.7)); independence = Liouville on S² [D]; rank 2 = DGRS Prop 7.7 + bounded-twist rank constancy [V] | [D] (independence) |
| `hdet₁` | det A₁(p) ≠ 0 for all p: the degree-1 frame is nondegenerate against the dual functionals | choice of frame: dual frame at (0,0), parameters retracted into the region where it stays invertible | [def] |
| `hdet₂` | det A₂(p) ≠ 0 for all p: the degree-2 frame | same | [def] |
| `h422` | `FirstVariation422`: det B ≠ 0; B·∂_τM(0,0) = !![0,0;0,p] with ∂_τM = `Mτ M` | CDDP Lemma 2.2 + 2.10; CDDP (4.22) with (4.38) | [V] |
| `hr₀` | r₀ := Bcc·p/det B > 0 | CDDP (1.3) non-degeneracy for b ∈ O (Thm 1(2)); sign = orientation of τ | [V] |
| `hdouble` | `DoublePoint`: s*(0) = 0, s* continuous at 0, s*(θ) < 0 for θ ≠ 0 | s* = −1+√(1−μ₀): DGRS (7.6) + BuOl Cor 5.1 + DFG Thm 2; μ₀ = θ²‖ω‖²/vol + O(θ⁴) (Kato–Rellich) | [V] |
| `hmirror` | charpoly A(θ,0) = (z − s*)³(z + s*): the degree-2 cluster at g_hyp is the locked pair at s* plus the pure pair at ±s* | DGRS (7.6) k = 2 with BuOl scalar zeros [V]; the −s* state identified as f'·ω_s [D] | [V]+[D] |
| `hpinning` | `Pinned`: det M(0,τ) = 0; charpoly A(0,τ) = z³(z − tr M(0,τ)) — at ρ_triv the degree-2 cluster is {0,0,0,twin} | CDDP Cor 4.1 via Thm 1(2), m_{2,0}(0) = b₁+2 = 3; the fourth eigenvalue = the lifted twin (DGRS Lemma 7.1) | [V] |
| `hlocked` | every eigenvalue of M(θ,τ) is an eigenvalue of A(θ,τ) — the locked branches | DGRS Lemma 7.1 (d₀ commutes with L_X); ∧dα lifts the closed branch | [V] |
| `hτR` | τ_R(χ_θ) ≠ 0, Reidemeister torsion of the acyclic χ_θ | Fried 1986 at g_hyp | [V] |
| `hfactor` | `ZetaFactorization`: ζ₀ = F·z/s_nc off the crossing, F continuous at the crossing, ζ₀(σ) = F(σ) at it (the cluster factor is λ/λ) | Chaubet–Dang (6.5) read at λ = 0 along the conformal family | [V] |
| `hfried_off` | off the crossing ζ₀(τ) = ζ(0; g_τ) = τ_R | DGRS Thm 2 local constancy of ζ(0) + Fried at g_hyp | [V] |
| `hexact` | at each crossing inside \|τ\| < δ the reduced complex C₀¹ → C₀² → C₀³ is exact (C₀¹ = `resZero₁ M θ σ`, C₀² = `resZero₂ A θ σ`, C₀³ = V₃) | Dang–Rivière Thm 2.1 / DGRS (7.1) | [V] |
| `hacyc` | c₀ = c₄ = 0 | DGRS Lemma 7.4 (+ ⋆) for acyclic unitary ρ | [V] |
| `hdual` | c₃ = c₁ | ⋆-duality, DGRS Lemma 7.2 | [V] |
| `hdims` | c_k = dim C₀^k for k = 1, 2, 3 at each crossing (k = 1, 2: dimensions of `resZero₁/₂` = algebraic multiplicities of 0 by Mathlib; k = 3: dim V₃) | bookkeeping | [def] |

**The analytic inputs inside F₁, F₂ (`Scale.ResolventFamily`, one row per field):**

| field | says | source | status |
|---|---|---|---|
| `bdd` | ‖R n x‖ bounded locally uniformly in the parameter x = (θ,τ,λ), on every level n | CDDP Lemma 4.3: the resolvent is bounded locally uniformly in τ, λ outside the resonance set; θ affine bounded twist | [V] |
| `inv_left`, `inv_right` | R n x is a two-sided inverse of the generator B n x = P(θ,τ) − λ modulo the inclusion | CDDP Lemma 4.3: Fredholm with inverse R(λ) on H^{r,s} for r > C₀ + \|s\| | [V] |
| `smooth` | x ↦ B n x is C^∞ into L(H (n+1), H n) | affine in θ and λ; smooth in τ (L_{X_τ} for the conformal family) | [V]-grade standard |
| `R_incl`, `B_incl` | resolvent and generator commute with the inclusions of the scale | the scale is one operator on nested spaces | [def] |
| `J`, `J_sq`, `J_incl` (`ComplexStructure`) | multiplication by i on each level | the spaces are complex | [def] |
| retraction | the families are pulled back by smooth retractions of (θ,τ) into a neighbourhood of (0,0) and of λ into an annulus around the contour where the resolvent exists | CDDP §4.2 fixed resonance-free contour | [def] |

Conclusion: ∃ K₁ > 0 and θ₀, δ > 0 such that for 0 < |θ| < θ₀: a unique crossing σ ∈ (0, 2|s*|/r₀], ζ of
order 0 at 0, the zero's slope ∂_τe₂/e₁ with |·| > 2r₀ ≥ the pole's, |e₁(θ,σ)| ≤ K₁|θ|σ, and
ζ₀(σ) = τ_R·(pole rate)/(zero rate) ≠ τ_R with the cluster-torsion identity.

The ledger table is hand-written; `python3 scripts/ledger_check.py` checks that the set of binders in the
theorem equals the set of rows.

## Working on the suite

- Zero `sorry`s in the development; the only `sorry` is the one Comparator expects in `Challenge.lean`.
- Grep Mathlib for names, never guess: `grep -rn "theorem <name>" .lake/packages/mathlib/Mathlib/`.
- Default heartbeat budget only; split declarations instead of raising it.
- Never hand-edit `Challenge.lean`; edit `B1s/fried_statement_defs_9_14.lean` (append only) and regenerate.
- Dates in filenames are creation dates; content is appended in dated sections.

## License

Apache-2.0, see `LICENSE`.
'''

def write_readme():
    (ROOT / "README.md").write_text(README); print("wrote README.md")

if __name__ == "__main__":
    remove_programme(); write_root_imports(); trim_yaml_scope(); write_readme()
    print("done — now: python3 scripts/make_challenge.py --check && python3 scripts/ledger_check.py")
