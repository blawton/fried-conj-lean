/-
ROUTE (ii) AT CORRELATION GRADE — THE ISOMETRY OBSTRUCTION AND THE JOINT-REGIME
INTERCHANGE (8/28). One of three sibling files on route (ii) (Front Page ¶3): A =
attainment/spectral-set grade, B = resolvent/holomorphic-limit grade, THIS FILE (C) =
correlation grade. Context: at b = ∞ the twisted flow semigroup is an ISOMETRY on L²
(volume-preserving flow, unitary twist), so OPERATOR-NORM decay cannot pass to the
limit; individual correlations ⟨e^{-tL}u, v⟩ against fixed smooth vectors DO decay for
mixing flows. This file machine-checks both halves of that obstruction/rescue, in the
honest scalar form where the content lives:

  c1_no_uniform_C_at_isometric_endpoint
      — NEGATIVE, fully elementary: pointwise convergence of norms to the isometric
        value 1 (strong convergence at the endpoint) is INCONSISTENT with a b-uniform
        bound n_b(t) ≤ C·e^{-βt}. Consequence for the note: the V4 working display
        (hypothesis_v4_working_8_17.md §1, "C, β independent of b ∈ (0,∞]") must NOT
        be read at operator-norm grade with C uniform through the endpoint — the
        polynomial prefactor in the posed Tao–Zworski form (their ν^{-K}, our b^K;
        arXiv:2311.01000 §1 display, harvested in V4 §1b) is FORCED, and the working
        display must carry it when the verbatim quote replaces it.
  c1_prefactor_escape
      — the matching consistency witness: an explicit family n_b(t) = min(1, b·e^{-t})
        satisfies BOTH the isometric-endpoint convergence AND the prefactor-form bound
        n_b(t) ≤ C·b^K·e^{-βt} (C = 1, K = 1, β = 1). So C1 kills exactly the
        uniform-C reading, not the corrected (posed) display.
  c2_endpoint_correlation_decay
      — POSITIVE (the route-(ii) interchange at correlation grade): from (a) H in the
        posed prefactor form for the correlation moduli c_b, and (b) a QUANTIFIED
        stochastic-stability rate |c_∞(t) − c_b(t)| ≤ E(b,t) together with a schedule
        b(t) → ∞ along which the error decays exponentially and the prefactor is
        dominated by half the gap, conclude exponential decay of the ENDPOINT
        correlation: c_∞(t) ≤ (A + C)·e^{-min(δ, β/2)·t} eventually.

RESEARCH PAYOFF (for the note; report, do not assume): C2's hypothesis h_err/h_sched
shows that route (ii) at correlation grade needs a QUANTIFIED convergence rate in b
(locally in t) from stochastic stability — a schedule can only be run through an
explicit error modulus E(b,t) — whereas the spectral-grade siblings consume only
qualitative convergence of resonances (cf. `hpt` in endpoints_8_20.lean, a bare
Tendsto). ⚡READ #3 ANSWER (9/01): Drouot [Dr17] does NOT provide a quantified
semigroup/correlation modulus — Thm 5 is spectral/resolvent only ⇒ route (ii) runs
at grade A (or B), never C, on this citation (vault drouot_read_3_9_01.md §3).

⚡THE GRADE LADDER (8/28 peer check-in; what each route-(ii) grade demands of Drouot):
  A (attainment/spectral-set, route_ii_attainment_8_28.lean)  — per-point attainment
    on compacts: QUALITATIVE convergence suffices (singleton compacts).
  B (resolvent/holomorphic, route_ii_resolvent_8_28.lean)     — TendstoLocallyUniformlyOn:
    QUALITATIVE loc-uniform convergence suffices (and the uniform family bound is
    derivable there, so H is not double-counted).
  C (correlation, THIS FILE)                                  — QUANTIFIED rate E(b,t)
    + schedule: the strongest demand, and the only grade that survives the endpoint
    isometry at norm level. C1 + its witness upgrade the siblings' docstring
    grade-warnings into a machine-checked fact: below correlation grade, uniform-C
    through the endpoint is FALSE, not merely unproved.

DESIGN CHOICES (documented per the brief):
  • Powers are real powers (Real.rpow, `b ^ K` with K : ℝ) to match the printed
    ν^{-K}. No positivity side conditions are consumed: the prefactor appears only on
    the LARGE side of inequalities, so K ≥ 0 and b ≥ 1 are semantic (they make the
    hypotheses satisfiable/meaningful) but never formally required.
  • Nonnegativity of the correlation moduli is NOT assumed — the triangle-inequality
    chain never needs it; likewise δ > 0 and β > 0 are meaning, not mechanism, in C2
    (the conclusion is a true inequality for any real rates; positivity is what makes
    it a DECAY statement), so they are not binders (unused-hypothesis hygiene). In C1,
    β > 0 IS mechanism — it is what buys a time with C·e^{-βt} < 1.
  • Citations enter as NAMED HYPOTHESES of theorems (house style, endpoints_8_20):
    never axioms, never sorries.
-/
import Mathlib

set_option linter.style.header false

namespace FriedRouteIIC

open Filter Topology

/-! ### §1 C1 — the isometry obstruction (negative direction) -/

/-- **C1 (NEGATIVE).** The uniform-C reading of H through the isometric endpoint is
INCONSISTENT. Here `n b t` stands for ‖e^{-tL_b} u‖ for a fixed unit vector u.

Hypotheses and what they cite:
  `hiso`  — strong convergence at the isometric endpoint: for each fixed t ≥ 0,
            n_b(t) → 1 as b → ∞. This is the scalar shadow of "the twisted flow
            semigroup at b = ∞ is an isometry on L² (volume-preserving flow, unitary
            twist) and e^{-tL_b} → e^{-tL_∞} strongly" — the stochastic-stability
            convergence direction [Drouot Dr17 — grade C NOT in print, read #3 9/01], evaluated on
            a fixed unit
            vector.
  `hunif` — the b-uniform decay reading of the V4 working display
            (hypothesis_v4_working_8_17.md §1): C, β independent of b, eventually in
            b, at operator-norm grade (hence on every unit vector).

Conclusion: `False`. Proof shape: pick t₀ with C·e^{-βt₀} < 1 and pass `hiso` to the
limit through `hunif`.

PURPOSE (the correction this theorem forces): the program's V4 working display claims
"C independent of b" INCLUDING the endpoint b = ∞. This theorem machine-checks that
reading as inconsistent — so the polynomial prefactor b^K in the posed Tao–Zworski
form (arXiv:2311.01000 §1, their ν^{-K}) is FORCED, and the working display must
carry it when the verbatim quote replaces it (V4 §3 checklist). See
`c1_prefactor_escape` for the witness that the prefactor form survives. -/
theorem c1_no_uniform_C_at_isometric_endpoint
    (n : ℝ → ℝ → ℝ) (C β : ℝ) (hC : 1 ≤ C) (hβ : 0 < β)
    (hiso : ∀ t : ℝ, 0 ≤ t → Tendsto (fun b => n b t) atTop (𝓝 1))
    (hunif : ∀ᶠ b in atTop, ∀ t : ℝ, 0 ≤ t → n b t ≤ C * Real.exp (-β * t)) :
    False := by
  -- the time at which the uniform bound dips strictly below the isometric value
  set t₀ : ℝ := (Real.log C + 1) / β with ht₀def
  have hC0 : (0 : ℝ) < C := lt_of_lt_of_le one_pos hC
  have hlogC : 0 ≤ Real.log C := Real.log_nonneg hC
  have ht₀ : 0 ≤ t₀ := div_nonneg (by linarith) hβ.le
  have hval : C * Real.exp (-β * t₀) = Real.exp (-1) := by
    have harg : -β * t₀ = -Real.log C + -1 := by
      rw [ht₀def]; field_simp; ring
    rw [harg, Real.exp_add, Real.exp_neg, Real.exp_log hC0]
    field_simp
  have hev : ∀ᶠ b in atTop, n b t₀ ≤ Real.exp (-1) := by
    filter_upwards [hunif] with b hb
    exact le_trans (hb t₀ ht₀) (le_of_eq hval)
  have hle : (1 : ℝ) ≤ Real.exp (-1) := le_of_tendsto (hiso t₀ ht₀) hev
  have hlt : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  linarith

/-- **C1′ (the escape hatch, witnessed).** The prefactor form is CONSISTENT with the
isometric endpoint: the explicit family n_b(t) = min(1, b·e^{-t}) converges to 1
pointwise in t as b → ∞ (the isometric endpoint) AND satisfies the posed-form bound
n_b(t) ≤ C·b^K·e^{-βt} with C = 1, K = 1, β = 1 (real power, matching
`c2_endpoint_correlation_decay`'s `hH`). Together with C1 this pins the correction
EXACTLY: uniform-C dies, ν^{-K} survives — the b^K prefactor is not an artifact of
the proof but the unique reading compatible with the endpoint isometry. -/
theorem c1_prefactor_escape :
    ∃ n : ℝ → ℝ → ℝ,
      (∀ t : ℝ, 0 ≤ t → Tendsto (fun b => n b t) atTop (𝓝 1)) ∧
      (∀ b : ℝ, 1 ≤ b → ∀ t : ℝ, 0 ≤ t →
        n b t ≤ 1 * b ^ (1 : ℝ) * Real.exp (-1 * t)) := by
  refine ⟨fun b t => min 1 (b * Real.exp (-t)), ?_, ?_⟩
  · intro t _
    have hev : (fun b => min 1 (b * Real.exp (-t))) =ᶠ[atTop] fun _ => (1 : ℝ) := by
      filter_upwards [eventually_ge_atTop (Real.exp t)] with b hb
      have h1 : Real.exp t * Real.exp (-t) ≤ b * Real.exp (-t) :=
        mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
      rw [← Real.exp_add] at h1
      simp only [add_neg_cancel, Real.exp_zero] at h1
      exact min_eq_left h1
    exact Tendsto.congr' hev.symm tendsto_const_nhds
  · intro b _ t _
    simp only [one_mul, Real.rpow_one, neg_one_mul]
    exact min_le_right (1 : ℝ) (b * Real.exp (-t))

/-! ### §2 C2 — the joint-regime interchange (positive direction) -/

/-- **C2 (POSITIVE) — route (ii) at correlation grade.** For correlation moduli
`c b t` (= |⟨e^{-tL_b}u, v⟩| against fixed smooth vectors) and `cInf t` (the same at
the b = ∞ geodesic flow), endpoint exponential decay FOLLOWS from finite-b data plus
a quantified rate. Hypotheses and their citation shapes:

  `hH`     — H in the POSED form (Tao–Zworski arXiv:2311.01000 §1 display, kinetic-BM
             variant per their §1 remark, twisted extension flagged; grade C for the
             scalar print, our extension flagged per V4 §1b): for all b ≥ b₁ and all
             t ≥ 0, c_b(t) ≤ C·b^K·e^{-βt}. Real power b^K; K ≥ 0 and b₁ ≥ 1 are
             semantic, never consumed.
  `hE`     — the error-modulus form of two-directional stochastic stability at
             correlation grade [Drouot Dr17; ⚡read #3 9/01: NOT provided — vault
             drouot_read_3_9_01.md §3]:
             |c_∞(t) − c_b(t)| ≤ E(b,t). ⚡THE QUANTIFIED SHAPE IS THE POINT: the
             spectral-grade siblings consume only qualitative Tendsto (cf. `hpt` in
             endpoints_8_20.lean); correlation grade cannot run a schedule through a
             bare limit — read #3 must record whether Dr17 gives E(b,t) explicitly.
  `hb, h_err, h_pow` — the SCHEDULE: b(t) → ∞ with, eventually in t, the error along
             the schedule exponentially small (E(b(t),t) ≤ A·e^{-δt}) and the
             prefactor dominated by half the gap (b(t)^K ≤ e^{βt/2}). Existence of
             such a schedule is exactly the compatibility condition between the loss
             exponent K and the error modulus (the budget's T(b) discipline).

Conclusion: eventually in t, c_∞(t) ≤ (A + C)·e^{-min(δ, β/2)·t}. Proof shape:
c_∞(t) ≤ |c_∞(t) − c_{b(t)}(t)| + c_{b(t)}(t), then each summand by its hypothesis,
then e^{βt/2}·e^{-βt} = e^{-βt/2} and both rates ≥ min(δ, β/2).

This is the correlation-grade endpoint clause DERIVED, not assumed — the route-(ii)
move — at the grade where the isometry obstruction (C1) permits it. -/
theorem c2_endpoint_correlation_decay
    (c : ℝ → ℝ → ℝ) (cInf : ℝ → ℝ) (E : ℝ → ℝ → ℝ)
    (C K β b₁ A δ : ℝ) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hH : ∀ b, b₁ ≤ b → ∀ t, 0 ≤ t → c b t ≤ C * b ^ K * Real.exp (-β * t))
    (hE : ∀ b t, |cInf t - c b t| ≤ E b t)
    (B : ℝ → ℝ) (hb : Tendsto B atTop atTop)
    (h_err : ∀ᶠ t in atTop, E (B t) t ≤ A * Real.exp (-δ * t))
    (h_pow : ∀ᶠ t in atTop, (B t) ^ K ≤ Real.exp (β * t / 2)) :
    ∀ᶠ t in atTop, cInf t ≤ (A + C) * Real.exp (-(min δ (β / 2)) * t) := by
  filter_upwards [hb.eventually_ge_atTop b₁, eventually_ge_atTop (0 : ℝ), h_err, h_pow]
    with t hbt ht herr hpow
  -- split against the finite-b correlation at the scheduled b(t)
  have h1 : cInf t ≤ E (B t) t + c (B t) t := by
    have h := (le_abs_self (cInf t - c (B t) t)).trans (hE (B t) t)
    linarith
  -- H in the posed form at b = B t
  have h3 : c (B t) t ≤ C * (B t) ^ K * Real.exp (-β * t) := hH (B t) hbt t ht
  -- the schedule eats the prefactor, leaving half the gap
  have h4 : C * (B t) ^ K * Real.exp (-β * t)
      ≤ C * Real.exp (β * t / 2) * Real.exp (-β * t) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC) (Real.exp_pos _).le
  have h5 : C * Real.exp (β * t / 2) * Real.exp (-β * t)
      = C * Real.exp (-(β / 2) * t) := by
    have harg : β * t / 2 + -β * t = -(β / 2) * t := by ring
    rw [mul_assoc, ← Real.exp_add, harg]
  -- both rates dominate the common rate min(δ, β/2)
  have h6 : Real.exp (-δ * t) ≤ Real.exp (-(min δ (β / 2)) * t) := by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_right (min_le_left δ (β / 2)) ht
    linarith
  have h7 : Real.exp (-(β / 2) * t) ≤ Real.exp (-(min δ (β / 2)) * t) := by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_right (min_le_right δ (β / 2)) ht
    linarith
  have hA1 : A * Real.exp (-δ * t) ≤ A * Real.exp (-(min δ (β / 2)) * t) :=
    mul_le_mul_of_nonneg_left h6 hA
  have hC1 : C * Real.exp (-(β / 2) * t) ≤ C * Real.exp (-(min δ (β / 2)) * t) :=
    mul_le_mul_of_nonneg_left h7 hC
  have hdist : (A + C) * Real.exp (-(min δ (β / 2)) * t)
      = A * Real.exp (-(min δ (β / 2)) * t) + C * Real.exp (-(min δ (β / 2)) * t) := by
    ring
  linarith

end FriedRouteIIC
