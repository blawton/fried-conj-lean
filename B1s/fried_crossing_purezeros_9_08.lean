/-
THE PURE DEGREE-2 ZEROS FROM THE RANK-4 CLUSTER — hrate_zero derived (9/08).

Companion to `fried_crossing_rate_9_07` / `fried_crossing_firstvariation_9_08` (same leg). The
capstones so far consume `hrate_zero`: "at the crossing the pure degree-2 zero arrives linearly
with a slope a ≠ 0 different from the pole's". This file derives it from the rank-4 cluster.

Objects. The degree-2 Riesz projector Π₂(θ,τ) onto the disc has rank 4; its characteristic
polynomial is P(z) = z⁴ − c₁z³ + c₂z² − c₃z + c₄ with c_i polynomial in the matrix entries. Two
roots are LOCKED to the lower-degree clusters: s_cl (f·dα = d₀²f/s_cl) and s_nc (d₀u_nc). Dividing
P by (z − s_cl)(z − s_nc) leaves the quadratic Q(z) = z² − e₁z + e₂ of the two PURE degree-2
branches, with e₁ = c₁ − s_cl − s_nc and e₂ = c₂ − s_cl s_nc − (s_cl + s_nc)e₁ — explicit
polynomials (§1). The argument never touches the branches themselves (they are not smooth at the
Jordan corner (0,0)); only e₁, e₂.

Inputs consumed (all named, all already in the ledger):
  (B₄) regularity of e₁, e₂ jointly in (θ,τ) near (0,0) — e₁ with a bounded mixed partial ∂_θ∂_τe₁
       (joint C²), e₂ with ∂²_τe₂ having a bounded θ-derivative (joint C³ in the τ,τ,θ directions);
       THIS is the rank-4 half of input (B), stated for the first time as what is actually used;
  (A)  mirror at g_hyp: e₁(θ,0) = 0, e₂(θ,0) = −s*(θ)² (pure zeros at ±s*);
  (D)  pinning at ρ_triv (CDDP Cor 4.1): e₁(0,τ) = e₂(0,τ) = 0;
  (E)  exactness at the crossing: e₂(θ,σ) = 0, i.e. a pure zero sits at 0 when the pole does;
  generic case e₁(θ,σ) ≠ 0 (else c₂ = 3 — the degenerate alternative, not treated here);
  the crossing data from the rate file: σ ∈ (0, 2|s*|/r₀], pole slope ∈ [r₀/2, 2r₀].

Outputs (§2–§4, PROVED): |e₁(θ,σ)| ≤ K₁|θ|σ = O(θ³) (two-variable Hadamard from the two axes;
with evenness one gets θ⁴ — NOT needed); |∂_τe₂(θ,σ)| ≥ r₀|s*|/4 (mean value on [0,σ] from
e₂(θ,0) = −s*², e₂(θ,σ) = 0, then the O(θ)-smallness of ∂²_τe₂ transfers the value from the
interior point to σ); hence the zero's slope ∂_τe₂/e₁ exceeds 2r₀ ≥ pole slope in absolute value
for small θ — the zero is STEEPER than the pole (main note §5.2, rederivation A6). The pure-zero
branch z through 0 is characterised as a continuous root of Q with z(σ) = 0 and is shown to
coincide near σ with the explicit root (w₋ or w₊), hence differentiable at σ with that slope
(`hasDerivAt_zero_branch`). §5 assembles the capstone `fried_fails_at_crossing_of_pure_zero_inputs`
in which `hrate_zero` is GONE.

⚡SHARPENING recorded here: the counterexample needs only e₁(θ,σ) = o(|s*|) = o(θ²), which C²
regularity (bounded mixed partial) already gives as O(θ³). Analyticity / C³ / evenness only sharpen
κ(θ) from O(θ) to O(θ²). Deposit v0.1 says "analyticity claimed, C³ used" — v0.2 should say C².

⚡AUDIT CRITERION: ZERO axioms of its own — `#print axioms` on every theorem = built-ins only.
-/
import B1s.fried_crossing_firstvariation_9_08

set_option linter.style.header false

namespace FriedCrossing

open Filter Topology

namespace PureZeros

open TwinRate

/-! ## §1 Quartic division: the pure quadratic factor -/

/-- P(z) = z⁴ − c₁z³ + c₂z² − c₃z + c₄, the characteristic polynomial of the rank-4 cluster. -/
def quartic (c₁ c₂ c₃ c₄ z : ℝ) : ℝ := z ^ 4 - c₁ * z ^ 3 + c₂ * z ^ 2 - c₃ * z + c₄

/-- e₁ = sum of the two pure roots = c₁ − s_cl − s_nc. -/
def e₁of (c₁ scl snc : ℝ) : ℝ := c₁ - scl - snc

/-- e₂ = product of the two pure roots = c₂ − s_cl s_nc − (s_cl + s_nc) e₁. -/
def e₂of (c₁ c₂ scl snc : ℝ) : ℝ := c₂ - scl * snc - (scl + snc) * e₁of c₁ scl snc

def rem₁ (c₁ c₂ c₃ scl snc : ℝ) : ℝ :=
  c₃ - ((scl + snc) * e₂of c₁ c₂ scl snc + scl * snc * e₁of c₁ scl snc)

def rem₀ (c₁ c₂ c₄ scl snc : ℝ) : ℝ := c₄ - scl * snc * e₂of c₁ c₂ scl snc

/-- Division with remainder: P = (z − s_cl)(z − s_nc)·Q − rem₁·z + rem₀. -/
theorem quartic_div (c₁ c₂ c₃ c₄ scl snc z : ℝ) :
    quartic c₁ c₂ c₃ c₄ z =
      (z - scl) * (z - snc) * (z ^ 2 - e₁of c₁ scl snc * z + e₂of c₁ c₂ scl snc)
        - rem₁ c₁ c₂ c₃ scl snc * z + rem₀ c₁ c₂ c₄ scl snc := by
  simp only [quartic, e₁of, e₂of, rem₁, rem₀]; ring

/-- If the two locked branches are distinct roots of P, the remainder vanishes. -/
theorem rem_eq_zero {c₁ c₂ c₃ c₄ scl snc : ℝ} (hne : scl ≠ snc)
    (h1 : quartic c₁ c₂ c₃ c₄ scl = 0) (h2 : quartic c₁ c₂ c₃ c₄ snc = 0) :
    rem₁ c₁ c₂ c₃ scl snc = 0 ∧ rem₀ c₁ c₂ c₄ scl snc = 0 := by
  have e1 := quartic_div c₁ c₂ c₃ c₄ scl snc scl
  have e2 := quartic_div c₁ c₂ c₃ c₄ scl snc snc
  rw [h1] at e1
  rw [h2] at e2
  have h3 : rem₁ c₁ c₂ c₃ scl snc * (scl - snc) = 0 := by linear_combination e1 - e2
  have hr1 : rem₁ c₁ c₂ c₃ scl snc = 0 := by
    rcases mul_eq_zero.mp h3 with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h) hne
  refine ⟨hr1, ?_⟩
  linear_combination -e1 + scl * hr1

/-- P factors exactly through the pure quadratic. -/
theorem quartic_factor {c₁ c₂ c₃ c₄ scl snc : ℝ} (hne : scl ≠ snc)
    (h1 : quartic c₁ c₂ c₃ c₄ scl = 0) (h2 : quartic c₁ c₂ c₃ c₄ snc = 0) (z : ℝ) :
    quartic c₁ c₂ c₃ c₄ z =
      (z - scl) * (z - snc) * (z ^ 2 - e₁of c₁ scl snc * z + e₂of c₁ c₂ scl snc) := by
  obtain ⟨hr1, hr0⟩ := rem_eq_zero hne h1 h2
  rw [quartic_div, hr1, hr0, zero_mul, sub_zero, add_zero]

/-- The degree-2 resonances in the disc are exactly: the two locked branches and the roots of Q. -/
theorem quartic_roots {c₁ c₂ c₃ c₄ scl snc : ℝ} (hne : scl ≠ snc)
    (h1 : quartic c₁ c₂ c₃ c₄ scl = 0) (h2 : quartic c₁ c₂ c₃ c₄ snc = 0) (z : ℝ) :
    quartic c₁ c₂ c₃ c₄ z = 0 ↔
      z = scl ∨ z = snc ∨ z ^ 2 - e₁of c₁ scl snc * z + e₂of c₁ c₂ scl snc = 0 := by
  rw [quartic_factor hne h1 h2, mul_eq_zero, mul_eq_zero, sub_eq_zero, sub_eq_zero, or_assoc]

/-! ## §2 Two-variable Hadamard bounds -/

/-- f vanishes on both axes and has a bounded mixed partial ⇒ |f(θ,τ)| ≤ K|θ||τ|. -/
theorem abs_le_of_vanish_axes {f fτ fθτ : ℝ → ℝ → ℝ} {K ε : ℝ} (hε : 0 < ε)
    (h0τ : ∀ θ, f θ 0 = 0) (h0θ : ∀ τ, f 0 τ = 0)
    (hτ : ∀ θ τ, HasDerivAt (f θ) (fτ θ τ) τ)
    (hθ : ∀ θ τ, HasDerivAt (fun θ => fτ θ τ) (fθτ θ τ) θ)
    (hK : ∀ θ τ, |θ| < ε → |τ| < ε → |fθτ θ τ| ≤ K)
    {θ τ : ℝ} (hθε : |θ| < ε) (hτε : |τ| < ε) : |f θ τ| ≤ K * |θ| * |τ| := by
  have hK0 : 0 ≤ K :=
    le_trans (abs_nonneg _) (hK 0 0 (by simpa using hε) (by simpa using hε))
  have hfτ0 : ∀ ξ, fτ 0 ξ = 0 := fun ξ => by
    have h1 : HasDerivAt (f 0) (fτ 0 ξ) ξ := hτ 0 ξ
    have h2 : HasDerivAt (f 0) 0 ξ := by
      have : f 0 = fun _ => (0 : ℝ) := funext h0θ
      rw [this]; exact hasDerivAt_const ξ (0 : ℝ)
    exact h1.unique h2
  by_cases hτ0 : τ = 0
  · subst hτ0; rw [h0τ, abs_zero]; positivity
  obtain ⟨ξ, hξ, hslope⟩ := Hadamard.entry_slope_eq (hτ θ) hτ0
  rw [h0τ, sub_zero] at hslope
  have hfval : f θ τ = τ * fτ θ ξ := by rw [← hslope]; field_simp
  by_cases hθ0 : θ = 0
  · subst hθ0; rw [hfval, hfτ0, mul_zero, abs_zero]; positivity
  obtain ⟨η, hη, hslope2⟩ := Hadamard.entry_slope_eq (fun t => hθ t ξ) hθ0
  rw [hfτ0, sub_zero] at hslope2
  have hfτval : fτ θ ξ = θ * fθτ η ξ := by rw [← hslope2]; field_simp
  rw [hfval, hfτval, abs_mul, abs_mul]
  have hb := hK η ξ (lt_trans hη hθε) (lt_trans hξ hτε)
  calc |τ| * (|θ| * |fθτ η ξ|) ≤ |τ| * (|θ| * K) := by gcongr
    _ = K * |θ| * |τ| := by ring

/-- g vanishes on the axis θ = 0 and has a bounded θ-derivative ⇒ |g(θ,τ)| ≤ K|θ|. -/
theorem abs_le_of_vanish_θ {g gθ : ℝ → ℝ → ℝ} {K ε : ℝ} (hε : 0 < ε)
    (h0 : ∀ τ, g 0 τ = 0)
    (hθ : ∀ θ τ, HasDerivAt (fun θ => g θ τ) (gθ θ τ) θ)
    (hK : ∀ θ τ, |θ| < ε → |τ| < ε → |gθ θ τ| ≤ K)
    {θ τ : ℝ} (hθε : |θ| < ε) (hτε : |τ| < ε) : |g θ τ| ≤ K * |θ| := by
  have hK0 : 0 ≤ K :=
    le_trans (abs_nonneg _) (hK 0 0 (by simpa using hε) (by simpa using hε))
  by_cases hθ0 : θ = 0
  · subst hθ0; rw [h0, abs_zero]; positivity
  obtain ⟨η, hη, hslope⟩ := Hadamard.entry_slope_eq (fun t => hθ t τ) hθ0
  rw [h0, sub_zero] at hslope
  have hval : g θ τ = θ * gθ η τ := by rw [← hslope]; field_simp
  rw [hval, abs_mul]
  have hb := hK η τ (lt_trans hη hθε) hτε
  calc |θ| * |gθ η τ| ≤ |θ| * K := by gcongr
    _ = K * |θ| := by ring

/-- Derivatives of a function vanishing identically on a line vanish there too. -/
theorem deriv_zero_of_zero_fun {g gτ : ℝ → ℝ} (h0 : ∀ τ, g τ = 0)
    (hd : ∀ τ, HasDerivAt g (gτ τ) τ) (τ : ℝ) : gτ τ = 0 := by
  have h1 : HasDerivAt g 0 τ := by
    have : g = fun _ => (0 : ℝ) := funext h0
    rw [this]; exact hasDerivAt_const τ (0 : ℝ)
  exact (hd τ).unique h1

/-! ## §3 The estimates at the crossing -/

/-- THE ESTIMATES. At the crossing σ ∈ (0, 2|s*|/r₀] of a small θ:
(i) |e₁(θ,σ)| ≤ K₁|θ|σ (Hadamard from the two axes);
(ii) |∂_τe₂(θ,σ)| ≥ r₀|s*|/4 (mean value on [0,σ] from e₂(θ,0) = −s*², e₂(θ,σ) = 0, corrected
by the O(|θ|)-bound on ∂²_τe₂ transferred from the axis θ = 0);
(iii) hence, if e₁(θ,σ) ≠ 0, the zero's slope |∂_τe₂/e₁| > 2r₀. -/
theorem crossing_estimates
    (sStar : ℝ → ℝ) (e₁ e₂ e₁τ e₁θτ e₂τ e₂ττ e₂θττ : ℝ → ℝ → ℝ) {r₀ K₁ K₂ ε : ℝ}
    (hr₀ : 0 < r₀) (hK₁ : 0 < K₁) (hK₂ : 0 < K₂) (hε : 0 < ε)
    (hd₁ : ∀ θ τ, HasDerivAt (e₁ θ) (e₁τ θ τ) τ)
    (hd₁' : ∀ θ τ, HasDerivAt (fun θ => e₁τ θ τ) (e₁θτ θ τ) θ)
    (hB₁ : ∀ θ τ, |θ| < ε → |τ| < ε → |e₁θτ θ τ| ≤ K₁)
    (hd₂ : ∀ θ τ, HasDerivAt (e₂ θ) (e₂τ θ τ) τ)
    (hd₂' : ∀ θ τ, HasDerivAt (e₂τ θ) (e₂ττ θ τ) τ)
    (hd₂'' : ∀ θ τ, HasDerivAt (fun θ => e₂ττ θ τ) (e₂θττ θ τ) θ)
    (hB₂ : ∀ θ τ, |θ| < ε → |τ| < ε → |e₂θττ θ τ| ≤ K₂)
    (h₁τ0 : ∀ θ, e₁ θ 0 = 0) (h₁θ0 : ∀ τ, e₁ 0 τ = 0)
    (h₂τ0 : ∀ θ, e₂ θ 0 = -(sStar θ) ^ 2) (h₂θ0 : ∀ τ, e₂ 0 τ = 0)
    {θ σ : ℝ} (hθε : |θ| < ε) (hθ1 : |θ| < r₀ ^ 2 / (8 * K₂)) (hθ2 : |θ| < r₀ / (16 * K₁))
    (hs : sStar θ < 0) (hσpos : 0 < σ) (hσle : σ ≤ 2 * |sStar θ| / r₀) (hσε : σ < ε)
    (h₂σ : e₂ θ σ = 0) :
    |e₁ θ σ| ≤ K₁ * |θ| * σ ∧ r₀ * |sStar θ| / 4 ≤ |e₂τ θ σ| ∧
      (e₁ θ σ ≠ 0 → 2 * r₀ < |e₂τ θ σ / e₁ θ σ|) := by
  set S := |sStar θ| with hS
  have hSpos : 0 < S := abs_pos.mpr hs.ne
  have hσabs : |σ| < ε := by rw [abs_of_pos hσpos]; exact hσε
  -- (i)
  have hi : |e₁ θ σ| ≤ K₁ * |θ| * σ := by
    have := abs_le_of_vanish_axes hε h₁τ0 h₁θ0 hd₁ hd₁' hB₁ hθε hσabs
    rwa [abs_of_pos hσpos] at this
  -- ∂²_τ e₂ vanishes on θ = 0, hence is O(|θ|)
  have hττ0 : ∀ τ, e₂ττ 0 τ = 0 := by
    have hτ0 : ∀ τ, e₂τ 0 τ = 0 := deriv_zero_of_zero_fun h₂θ0 (hd₂ 0)
    exact deriv_zero_of_zero_fun hτ0 (hd₂' 0)
  have hττ_small : ∀ τ, |τ| < ε → |e₂ττ θ τ| ≤ K₂ * |θ| := fun τ hτ =>
    abs_le_of_vanish_θ hε hττ0 hd₂'' hB₂ hθε hτ
  -- mean value on [0, σ]: ∂_τe₂(θ,ξ) = s*²/σ
  have hcont₂ : ContinuousOn (e₂ θ) (Set.Icc 0 σ) := fun τ _ =>
    (hd₂ θ τ).continuousAt.continuousWithinAt
  obtain ⟨ξ, hξ, hξslope⟩ := exists_hasDerivAt_eq_slope (e₂ θ) (e₂τ θ) hσpos hcont₂
    (fun τ _ => hd₂ θ τ)
  rw [h₂σ, h₂τ0, sub_zero, zero_sub, neg_neg] at hξslope
  -- ∂_τe₂(θ,ξ) = S²/σ
  have hξval : e₂τ θ ξ = S ^ 2 / σ := by rw [hξslope, hS, sq_abs]
  -- mean value on [ξ, σ] for ∂_τe₂
  have hcont₂' : ContinuousOn (e₂τ θ) (Set.Icc ξ σ) := fun τ _ =>
    (hd₂' θ τ).continuousAt.continuousWithinAt
  obtain ⟨η, hη, hηslope⟩ := exists_hasDerivAt_eq_slope (e₂τ θ) (e₂ττ θ) hξ.2 hcont₂'
    (fun τ _ => hd₂' θ τ)
  have hηabs : |η| < ε := by
    rw [abs_of_pos (lt_trans hξ.1 hη.1)]; exact lt_trans hη.2 hσε
  have hdiff : |e₂τ θ σ - e₂τ θ ξ| ≤ K₂ * |θ| * σ := by
    have h1 : e₂τ θ σ - e₂τ θ ξ = e₂ττ θ η * (σ - ξ) := by
      rw [hηslope]; exact (div_mul_cancel₀ _ (sub_pos.mpr hξ.2).ne').symm
    rw [h1, abs_mul, abs_of_pos (sub_pos.mpr hξ.2)]
    calc |e₂ττ θ η| * (σ - ξ) ≤ (K₂ * |θ|) * σ :=
          mul_le_mul (hττ_small η hηabs) (by linarith [hξ.1]) (by linarith [hξ.2])
            (by positivity)
      _ = K₂ * |θ| * σ := by ring
  -- numeric bounds
  have hσinv : S * r₀ / 2 ≤ S ^ 2 / σ := by
    have h2S : 0 < 2 * S / r₀ := by positivity
    calc S * r₀ / 2 = S ^ 2 / (2 * S / r₀) := by field_simp
      _ ≤ S ^ 2 / σ := div_le_div_of_nonneg_left (sq_nonneg S) hσpos hσle
  have hK₂σ : K₂ * |θ| * σ ≤ r₀ * S / 4 := by
    have hθ1' : |θ| * (8 * K₂) < r₀ ^ 2 := (lt_div_iff₀ (by positivity)).mp hθ1
    calc K₂ * |θ| * σ ≤ K₂ * |θ| * (2 * S / r₀) := by gcongr
      _ = (|θ| * (8 * K₂)) * (S / (4 * r₀)) := by field_simp; ring
      _ ≤ r₀ ^ 2 * (S / (4 * r₀)) := by gcongr
      _ = r₀ * S / 4 := by field_simp
  have hii : r₀ * S / 4 ≤ |e₂τ θ σ| := by
    have h1 : |e₂τ θ ξ| - |e₂τ θ σ - e₂τ θ ξ| ≤ |e₂τ θ σ| := by
      have := abs_sub_abs_le_abs_sub (e₂τ θ ξ) (e₂τ θ σ)
      rw [abs_sub_comm] at this
      linarith
    have h2 : |e₂τ θ ξ| = S ^ 2 / σ := by
      rw [hξval, abs_of_pos (by positivity)]
    linarith
  refine ⟨hi, hii, fun he1 => ?_⟩
  -- (iii)
  have he1pos : 0 < |e₁ θ σ| := abs_pos.mpr he1
  have hU : |e₁ θ σ| ≤ 2 * K₁ * |θ| * S / r₀ := by
    calc |e₁ θ σ| ≤ K₁ * |θ| * σ := hi
      _ ≤ K₁ * |θ| * (2 * S / r₀) := by gcongr
      _ = 2 * K₁ * |θ| * S / r₀ := by ring
  have hθ2' : |θ| * (16 * K₁) < r₀ := (lt_div_iff₀ (by positivity)).mp hθ2
  have hkey : 2 * r₀ * |e₁ θ σ| < |e₂τ θ σ| := by
    calc 2 * r₀ * |e₁ θ σ| ≤ 2 * r₀ * (2 * K₁ * |θ| * S / r₀) := by gcongr
      _ = (|θ| * (16 * K₁)) * (S / 4) := by field_simp; ring
      _ < r₀ * (S / 4) := by gcongr
      _ = r₀ * S / 4 := by ring
      _ ≤ |e₂τ θ σ| := hii
  rw [abs_div]
  exact (lt_div_iff₀ he1pos).mpr hkey

/-! ## §4 The pure-zero branch through 0 -/

/-- ∂w₋/∂τ (mirror of `dwPlus`). -/
noncomputable def dwMinus (a b a' b' : ℝ) : ℝ :=
  (a' - (2 * a * a' - 4 * b') / (2 * Real.sqrt (disc a b))) / 2

theorem hasDerivAt_wMinus {A B : ℝ → ℝ} {a' b' τ : ℝ} (hA : HasDerivAt A a' τ)
    (hB : HasDerivAt B b' τ) (hD : 0 < disc (A τ) (B τ)) :
    HasDerivAt (fun t => wMinus (A t) (B t)) (dwMinus (A τ) (B τ) a' b') τ := by
  unfold wMinus dwMinus
  have hs : HasDerivAt (fun t => Real.sqrt (disc (A t) (B t)))
      ((2 * A τ * a' - 4 * b') / (2 * Real.sqrt (disc (A τ) (B τ)))) τ :=
    (hasDerivAt_disc hA hB).sqrt hD.ne'
  exact (hA.sub hs).div_const 2

theorem continuousAt_wMinus (p : ℝ × ℝ) :
    ContinuousAt (fun q : ℝ × ℝ => wMinus q.1 q.2) p := by
  unfold wMinus disc
  fun_prop

/-- At a point where b = 0 and a ≠ 0 the root through 0 has slope b'/a, whichever of w± it is. -/
theorem dwMinus_at_zero {a a' b' : ℝ} (ha : 0 < a) : dwMinus a 0 a' b' = b' / a := by
  have ha0 : a ≠ 0 := ha.ne'
  unfold dwMinus disc
  rw [mul_zero, sub_zero, Real.sqrt_sq ha.le]
  field_simp
  ring

theorem dwPlus_at_zero {a a' b' : ℝ} (ha : a < 0) : dwPlus a 0 a' b' = b' / a := by
  have ha0 : a ≠ 0 := ha.ne
  unfold dwPlus disc
  have : Real.sqrt (a ^ 2) = -a := by rw [Real.sqrt_sq_eq_abs, abs_of_neg ha]
  rw [mul_zero, sub_zero, this]
  field_simp
  ring

theorem wMinus_at_zero_nonneg {a : ℝ} (ha : 0 ≤ a) : wMinus a 0 = 0 := by
  unfold wMinus disc
  rw [mul_zero, sub_zero, Real.sqrt_sq ha]; ring

theorem wPlus_at_zero_neg {a : ℝ} (ha : a < 0) : wPlus a 0 = 0 := by
  unfold wPlus disc
  have : Real.sqrt (a ^ 2) = -a := by rw [Real.sqrt_sq_eq_abs, abs_of_neg ha]
  rw [mul_zero, sub_zero, this]; ring

theorem wPlus_at_zero_pos {a : ℝ} (ha : 0 < a) : wPlus a 0 = a := wPlus_at_cddp ha

theorem wMinus_at_zero_neg {a : ℝ} (ha : a < 0) : wMinus a 0 = a := by
  unfold wMinus disc
  have : Real.sqrt (a ^ 2) = -a := by rw [Real.sqrt_sq_eq_abs, abs_of_neg ha]
  rw [mul_zero, sub_zero, this]; ring

/-- THE PURE-ZERO BRANCH. A continuous root z of Q(τ; ·) = z² − e₁(τ)z + e₂(τ) with z(σ) = 0,
where e₂(σ) = 0 and e₁(σ) ≠ 0, coincides near σ with the explicit root vanishing at σ and is
differentiable there with slope ∂_τe₂(σ)/e₁(σ). -/
theorem hasDerivAt_zero_branch {e₁ e₂ z : ℝ → ℝ} {e₁' e₂' σ : ℝ}
    (hd₁ : HasDerivAt e₁ e₁' σ) (hd₂ : HasDerivAt e₂ e₂' σ)
    (h₂σ : e₂ σ = 0) (h₁σ : e₁ σ ≠ 0)
    (hzQ : ∀ τ, z τ ^ 2 - e₁ τ * z τ + e₂ τ = 0) (hzc : ContinuousAt z σ) (hz0 : z σ = 0) :
    HasDerivAt z (e₂' / e₁ σ) σ := by
  have hc₁ : ContinuousAt e₁ σ := hd₁.continuousAt
  have hc₂ : ContinuousAt e₂ σ := hd₂.continuousAt
  have hpair : ContinuousAt (fun τ => (e₁ τ, e₂ τ)) σ := hc₁.prodMk hc₂
  have hDσ : 0 < disc (e₁ σ) (e₂ σ) := by
    unfold disc; rw [h₂σ, mul_zero, sub_zero]; positivity
  have hDc : ContinuousAt (fun τ => disc (e₁ τ) (e₂ τ)) σ := by
    unfold disc
    exact (hc₁.pow 2).sub (continuousAt_const.mul hc₂)
  have hevD : ∀ᶠ τ in 𝓝 σ, 0 < disc (e₁ τ) (e₂ τ) := hDc.eventually (lt_mem_nhds hDσ)
  -- z is one of the two explicit roots wherever the discriminant is nonnegative
  have hroots : ∀ τ, 0 ≤ disc (e₁ τ) (e₂ τ) →
      z τ = wPlus (e₁ τ) (e₂ τ) ∨ z τ = wMinus (e₁ τ) (e₂ τ) := fun τ hD => by
    have h := (TwinRate.cluster_roots (sStar := 0) (τ := 1) hD (z τ)).mp
    simp only [TwinRate.clusterTrace, TwinRate.clusterDet, mul_zero, zero_add, one_mul,
      zero_mul, add_zero, one_pow, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      mul_one] at h
    exact h (hzQ τ)
  rcases lt_or_gt_of_ne h₁σ with hneg | hpos
  · -- e₁(σ) < 0: the root through 0 is w₊; w₋(σ) = e₁(σ) < 0
    have hwP : ContinuousAt (fun τ => wPlus (e₁ τ) (e₂ τ)) σ :=
      (continuousAt_wPlus _).comp hpair
    have hwM : ContinuousAt (fun τ => wMinus (e₁ τ) (e₂ τ)) σ :=
      (continuousAt_wMinus _).comp hpair
    have hwMσ : wMinus (e₁ σ) (e₂ σ) = e₁ σ := by rw [h₂σ]; exact wMinus_at_zero_neg hneg
    have hevM : ∀ᶠ τ in 𝓝 σ, wMinus (e₁ τ) (e₂ τ) < e₁ σ / 2 :=
      hwM.eventually_lt continuousAt_const
        (by change wMinus (e₁ σ) (e₂ σ) < e₁ σ / 2; rw [hwMσ]; linarith)
    have hevz : ∀ᶠ τ in 𝓝 σ, e₁ σ / 2 < z τ :=
      continuousAt_const.eventually_lt hzc (by change e₁ σ / 2 < z σ; rw [hz0]; linarith)
    have heq : z =ᶠ[𝓝 σ] fun τ => wPlus (e₁ τ) (e₂ τ) := by
      filter_upwards [hevD, hevM, hevz] with τ hD hM hz
      rcases hroots τ hD.le with h | h
      · exact h
      · exfalso; rw [h] at hz; linarith
    have hderiv : HasDerivAt (fun τ => wPlus (e₁ τ) (e₂ τ))
        (dwPlus (e₁ σ) (e₂ σ) e₁' e₂') σ := hasDerivAt_wPlus hd₁ hd₂ hDσ
    rw [h₂σ, dwPlus_at_zero hneg] at hderiv
    exact hderiv.congr_of_eventuallyEq heq
  · -- e₁(σ) > 0: the root through 0 is w₋; w₊(σ) = e₁(σ) > 0
    have hwP : ContinuousAt (fun τ => wPlus (e₁ τ) (e₂ τ)) σ :=
      (continuousAt_wPlus _).comp hpair
    have hwPσ : wPlus (e₁ σ) (e₂ σ) = e₁ σ := by rw [h₂σ]; exact wPlus_at_zero_pos hpos
    have hevP : ∀ᶠ τ in 𝓝 σ, e₁ σ / 2 < wPlus (e₁ τ) (e₂ τ) :=
      continuousAt_const.eventually_lt hwP
        (by change e₁ σ / 2 < wPlus (e₁ σ) (e₂ σ); rw [hwPσ]; linarith)
    have hevz : ∀ᶠ τ in 𝓝 σ, z τ < e₁ σ / 2 :=
      hzc.eventually_lt continuousAt_const (by change z σ < e₁ σ / 2; rw [hz0]; linarith)
    have heq : z =ᶠ[𝓝 σ] fun τ => wMinus (e₁ τ) (e₂ τ) := by
      filter_upwards [hevD, hevP, hevz] with τ hD hP hz
      rcases hroots τ hD.le with h | h
      · exfalso; rw [h] at hz; linarith
      · exact h
    have hderiv : HasDerivAt (fun τ => wMinus (e₁ τ) (e₂ τ))
        (dwMinus (e₁ σ) (e₂ σ) e₁' e₂') σ := hasDerivAt_wMinus hd₁ hd₂ hDσ
    rw [h₂σ, dwMinus_at_zero hpos] at hderiv
    exact hderiv.congr_of_eventuallyEq heq

end PureZeros

/-! ## §5 Capstones without `hrate_zero` -/
namespace Capstone

open TorsionCore OrderCount Crossing RateRatio TwinRate PureZeros

/-- `fried_fails_at_crossing_local` with the zero's arrival given as `LinearArrival`, and only
required at crossings inside |τ| < δ. -/
theorem fried_fails_at_crossing_local'
    {K : Type*} [Field K] {V₁ V₂ V₃ : Type*}
    [AddCommGroup V₁] [Module K V₁] [FiniteDimensional K V₁]
    [AddCommGroup V₂] [Module K V₂] [FiniteDimensional K V₂]
    [AddCommGroup V₃] [Module K V₃]
    (s ds z R : ℝ → ℝ) (c : Fin 5 → ℕ) (r δ τR : ℝ)
    (hτR : τR ≠ 0) (hr : 0 < r)
    (hs0 : s 0 < 0) (hsmall : |s 0| < r * δ)
    (hrate : ∀ τ, |τ| < δ → HasDerivAt s (ds τ) τ ∧ r ≤ ds τ)
    (hzero : ∀ τ₀, |τ₀| < δ → s τ₀ = 0 → ∃ a : ℝ, a ≠ 0 ∧ a ≠ ds τ₀ ∧ LinearArrival z a τ₀)
    (hcont : ∀ τ₀, s τ₀ = 0 → ContinuousAt R τ₀)
    (hfried_off : ∀ τ, |τ| < δ → s τ ≠ 0 → R τ * z τ / s τ = τR)
    (hexact : ∃ (f : V₁ →ₗ[K] V₂) (g : V₂ →ₗ[K] V₃), Function.Injective f ∧
      LinearMap.range f = LinearMap.ker g ∧ Function.Surjective g)
    (hacyc : c 0 = 0 ∧ c 4 = 0) (hdual : c 3 = c 1)
    (hdims : c 1 = Module.finrank K V₁ ∧ c 2 = Module.finrank K V₂ ∧
      c 3 = Module.finrank K V₃) :
    ∃ σ, 0 < σ ∧ σ ≤ |s 0| / r ∧ σ < δ ∧ s σ = 0 ∧ (∀ τ, |τ| < δ → s τ = 0 → τ = σ) ∧
      zetaOrder c = 0 ∧
      ∃ a ratio : ℝ, a ≠ 0 ∧ ds σ ≠ 0 ∧
        Tendsto (fun τ => s τ / z τ) (𝓝[≠] σ) (𝓝 ratio) ∧
        ratio = ds σ / a ∧ ratio ≠ 1 ∧ R σ = τR * ratio ∧ R σ ≠ τR ∧
        refinedTorsion 1 (ds σ / (a - ds σ)) = -(a / ds σ) := by
  obtain ⟨σ, hσpos, hσle, hσlt, hσ0, huniq⟩ :=
    crossing_exists_unique_local hr (fun τ hτ => (hrate τ hτ).1)
      (fun τ hτ => (hrate τ hτ).2) hs0 hsmall
  have hσabs : |σ| < δ := by rw [abs_lt]; constructor <;> linarith
  have hoff : ∀ᶠ τ in 𝓝[≠] σ, R τ * z τ / s τ = τR := by
    have hnear : ∀ᶠ τ in 𝓝 σ, |τ| < δ :=
      (continuous_abs.continuousAt (x := σ)).eventually (gt_mem_nhds hσabs)
    filter_upwards [eventually_ne_nhdsNE σ, nhdsWithin_le_nhds hnear] with τ hτ hτδ
    exact hfried_off τ hτδ fun h0 => hτ (huniq τ hτδ h0)
  obtain ⟨a, ha, hab, hzA⟩ := hzero σ hσabs hσ0
  have hpA : LinearArrival s (ds σ) σ := linearArrival_of_hasDerivAt (hrate σ hσabs).1 hσ0
  have hb : ds σ ≠ 0 := (lt_of_lt_of_le hr (hrate σ hσabs).2).ne'
  have hval : R σ = τR * (ds σ / a) :=
    crossing_value_local hzA hpA ha hb hoff (hcont σ hσ0)
  have hratio : ds σ / a ≠ 1 := fun h1 => hab ((div_eq_one_iff_eq ha).mp h1).symm
  obtain ⟨f, g, hf, hfg, hg⟩ := hexact
  have hord : zetaOrder c = 0 := order_zero_of_exact f g hf hfg hg c hacyc hdual hdims
  refine ⟨σ, hσpos, hσle, hσlt, hσ0, huniq, hord, a, ds σ / a, ha, hb,
    ratio_tendsto hpA hzA ha, rfl, hratio, hval, ?_, ?_⟩
  · rw [hval]; exact (crossing_value_ne_iff hτR ha).mpr fun h => hratio (by rw [h, div_self ha])
  · exact jordan_torsion_eq_neg_ratio (ds σ) a hb hab

/-- FRIED FAILS AT THE CROSSING — `hrate_zero` DERIVED. The pure degree-2 zero data enter only as:
the symmetric functions e₁, e₂ of the two pure branches with their joint regularity at (0,0)
(bounded ∂_θ∂_τe₁; bounded ∂_θ∂²_τe₂) [rank-4 half of input (B)], the boundary values e₁(θ,0) = 0,
e₂(θ,0) = −s*² [mirror, A], e₁(0,τ) = e₂(0,τ) = 0 [pinning, D], and at each crossing: e₂ = 0
[exactness, E], e₁ ≠ 0 [generic case], and z a continuous root of z² − e₁z + e₂ through 0 [the
pure-zero branch]. Everything else is the cluster capstone's ledger. Conclusion adds: the zero's
slope at the crossing is ∂_τe₂/e₁ and exceeds 2r₀ in absolute value (steeper than the pole). -/
theorem fried_fails_at_crossing_of_pure_zero_inputs
    {K : Type*} [Field K] {V₁ V₂ V₃ : Type*}
    [AddCommGroup V₁] [Module K V₁] [FiniteDimensional K V₁]
    [AddCommGroup V₂] [Module K V₂] [FiniteDimensional K V₂]
    [AddCommGroup V₃] [Module K V₃]
    -- the twin (rate file)
    (sStar : ℝ → ℝ) (a b a' b' : ℝ → ℝ → ℝ) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hderiv_a : ∀ θ τ, HasDerivAt (a θ) (a' θ τ) τ)
    (hderiv_b : ∀ θ τ, HasDerivAt (b θ) (b' θ τ) τ)
    (hcont_a : ContinuousAt (Function.uncurry a) (0, 0))
    (hcont_b : ContinuousAt (Function.uncurry b) (0, 0))
    (hcont_a' : ContinuousAt (Function.uncurry a') (0, 0))
    (hcont_b' : ContinuousAt (Function.uncurry b') (0, 0))
    (ha0 : a 0 0 = r₀) (hb0 : b 0 0 = 0)
    (hsStar0 : sStar 0 = 0) (hsStarc : ContinuousAt sStar 0)
    (hsStarneg : ∀ θ, θ ≠ 0 → sStar θ < 0)
    -- the pure degree-2 pair (this file)
    (e₁ e₂ e₁τ e₁θτ e₂τ e₂ττ e₂θττ : ℝ → ℝ → ℝ) {K₁ K₂ ε : ℝ}
    (hK₁ : 0 < K₁) (hK₂ : 0 < K₂) (hε : 0 < ε)
    (hd₁ : ∀ θ τ, HasDerivAt (e₁ θ) (e₁τ θ τ) τ)
    (hd₁' : ∀ θ τ, HasDerivAt (fun θ => e₁τ θ τ) (e₁θτ θ τ) θ)
    (hB₁ : ∀ θ τ, |θ| < ε → |τ| < ε → |e₁θτ θ τ| ≤ K₁)
    (hd₂ : ∀ θ τ, HasDerivAt (e₂ θ) (e₂τ θ τ) τ)
    (hd₂' : ∀ θ τ, HasDerivAt (e₂τ θ) (e₂ττ θ τ) τ)
    (hd₂'' : ∀ θ τ, HasDerivAt (fun θ => e₂ττ θ τ) (e₂θττ θ τ) θ)
    (hB₂ : ∀ θ τ, |θ| < ε → |τ| < ε → |e₂θττ θ τ| ≤ K₂)
    (h₁τ0 : ∀ θ, e₁ θ 0 = 0) (h₁θ0 : ∀ τ, e₁ 0 τ = 0)
    (h₂τ0 : ∀ θ, e₂ θ 0 = -(sStar θ) ^ 2) (h₂θ0 : ∀ τ, e₂ 0 τ = 0) :
    ∃ θ₀ δ : ℝ, 0 < θ₀ ∧ 0 < δ ∧ ∀ θ, θ ≠ 0 → |θ| < θ₀ →
      ∀ (z R : ℝ → ℝ) (c : Fin 5 → ℕ) (τR : ℝ),
        τR ≠ 0 →
        (∀ τ, z τ ^ 2 - e₁ θ τ * z τ + e₂ θ τ = 0) →
        (∀ τ₀, |τ₀| < δ → twin sStar a b θ τ₀ = 0 →
          ContinuousAt z τ₀ ∧ z τ₀ = 0 ∧ e₂ θ τ₀ = 0 ∧ e₁ θ τ₀ ≠ 0) →
        (∀ τ₀, twin sStar a b θ τ₀ = 0 → ContinuousAt R τ₀) →
        (∀ τ, |τ| < δ → twin sStar a b θ τ ≠ 0 → R τ * z τ / twin sStar a b θ τ = τR) →
        (∃ (f : V₁ →ₗ[K] V₂) (g : V₂ →ₗ[K] V₃), Function.Injective f ∧
          LinearMap.range f = LinearMap.ker g ∧ Function.Surjective g) →
        (c 0 = 0 ∧ c 4 = 0) → c 3 = c 1 →
        (c 1 = Module.finrank K V₁ ∧ c 2 = Module.finrank K V₂ ∧
          c 3 = Module.finrank K V₃) →
        ∃ σ, 0 < σ ∧ σ ≤ 2 * |sStar θ| / r₀ ∧ σ < δ ∧ twin sStar a b θ σ = 0 ∧
          (∀ τ, |τ| < δ → twin sStar a b θ τ = 0 → τ = σ) ∧
          zetaOrder c = 0 ∧
          -- the zero's slope: ∂_τe₂/e₁, steeper than the pole
          HasDerivAt z (e₂τ θ σ / e₁ θ σ) σ ∧ 2 * r₀ < |e₂τ θ σ / e₁ θ σ| ∧
          |e₁ θ σ| ≤ K₁ * |θ| * σ ∧
          ∃ α ratio : ℝ, α ≠ 0 ∧ dtwin (a θ σ) (b θ σ) (a' θ σ) (b' θ σ) σ ≠ 0 ∧
            Tendsto (fun τ => twin sStar a b θ τ / z τ) (𝓝[≠] σ) (𝓝 ratio) ∧
            ratio = dtwin (a θ σ) (b θ σ) (a' θ σ) (b' θ σ) σ / α ∧ ratio ≠ 1 ∧
            R σ = τR * ratio ∧ R σ ≠ τR ∧
            refinedTorsion 1 (dtwin (a θ σ) (b θ σ) (a' θ σ) (b' θ σ) σ /
              (α - dtwin (a θ σ) (b θ σ) (a' θ σ) (b' θ σ) σ)) =
              -(α / dtwin (a θ σ) (b θ σ) (a' θ σ) (b' θ σ) σ) := by
  obtain ⟨ε₁, hε₁, hrate⟩ := twin_rate_of_cluster sStar a b a' b' hr₀ hderiv_a hderiv_b
    hcont_a hcont_b hcont_a' hcont_b' ha0 hb0
  set δ := min ε₁ ε with hδdef
  have hδ : 0 < δ := lt_min hε₁ hε
  have hδε₁ : δ ≤ ε₁ := min_le_left _ _
  have hδε : δ ≤ ε := min_le_right _ _
  have hr2 : 0 < r₀ / 2 * δ := by positivity
  obtain ⟨θ₁, hθ₁, hsmall⟩ := Metric.continuousAt_iff.mp hsStarc (r₀ / 2 * δ) hr2
  set θ₀ := min (min ε₁ ε) (min (min (r₀ ^ 2 / (8 * K₂)) (r₀ / (16 * K₁))) θ₁) with hθ₀def
  have hθ₀ : 0 < θ₀ := by
    refine lt_min (lt_min hε₁ hε) (lt_min (lt_min ?_ ?_) hθ₁) <;> positivity
  refine ⟨θ₀, δ, hθ₀, hδ, fun θ hθne hθ z R c τR hτR hzQ hzc hcont hfried_off hexact hacyc
    hdual hdims => ?_⟩
  -- unpack the smallness of θ
  have hθε₁ : |θ| < ε₁ := lt_of_lt_of_le hθ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hθε : |θ| < ε := lt_of_lt_of_le hθ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hθ1 : |θ| < r₀ ^ 2 / (8 * K₂) := lt_of_lt_of_le hθ
    (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _)))
  have hθ2 : |θ| < r₀ / (16 * K₁) := lt_of_lt_of_le hθ
    (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _)))
  have hθ₁' : |θ| < θ₁ := lt_of_lt_of_le hθ (le_trans (min_le_right _ _) (min_le_right _ _))
  -- the twin's rate on |τ| < δ
  have hrateδ : ∀ τ, |τ| < δ →
      HasDerivAt (twin sStar a b θ) (dtwin (a θ τ) (b θ τ) (a' θ τ) (b' θ τ) τ) τ ∧
      r₀ / 2 ≤ dtwin (a θ τ) (b θ τ) (a' θ τ) (b' θ τ) τ := fun τ hτ =>
    ⟨(hrate θ τ hθε₁ (lt_of_lt_of_le hτ hδε₁)).2.1, (hrate θ τ hθε₁ (lt_of_lt_of_le hτ hδε₁)).2.2.1⟩
  have hs0 : twin sStar a b θ 0 < 0 := by rw [twin_zero]; exact hsStarneg θ hθne
  have hsmall' : |twin sStar a b θ 0| < r₀ / 2 * δ := by
    rw [twin_zero]
    have := hsmall (by rw [Real.dist_eq, sub_zero]; exact hθ₁')
    rw [Real.dist_eq, hsStar0, sub_zero] at this
    exact this
  -- the crossing
  obtain ⟨σ, hσpos, hσle, hσlt, hσ0, huniq⟩ :=
    crossing_exists_unique_local (by positivity : (0 : ℝ) < r₀ / 2)
      (fun τ hτ => (hrateδ τ hτ).1) (fun τ hτ => (hrateδ τ hτ).2) hs0 hsmall'
  rw [twin_zero] at hσle
  have hσle' : σ ≤ 2 * |sStar θ| / r₀ := by
    calc σ ≤ |sStar θ| / (r₀ / 2) := hσle
      _ = 2 * |sStar θ| / r₀ := by rw [div_div_eq_mul_div]; ring
  have hσabs : |σ| < δ := by rw [abs_lt]; constructor <;> linarith
  -- the pure zero at the crossing
  obtain ⟨hzcont, hz0, h₂σ, h₁σ⟩ := hzc σ hσabs hσ0
  obtain ⟨hi, _, hslope⟩ := crossing_estimates sStar e₁ e₂ e₁τ e₁θτ e₂τ e₂ττ e₂θττ hr₀ hK₁ hK₂ hε
    hd₁ hd₁' hB₁ hd₂ hd₂' hd₂'' hB₂ h₁τ0 h₁θ0 h₂τ0 h₂θ0 hθε hθ1 hθ2 (hsStarneg θ hθne) hσpos
    hσle' (lt_of_lt_of_le hσlt hδε) h₂σ
  have hbig := hslope h₁σ
  have hzderiv : HasDerivAt z (e₂τ θ σ / e₁ θ σ) σ :=
    hasDerivAt_zero_branch (hd₁ θ σ) (hd₂ θ σ) h₂σ h₁σ hzQ hzcont hz0
  -- the zero's slope is not the pole's
  have hzero : ∀ τ₀, |τ₀| < δ → twin sStar a b θ τ₀ = 0 →
      ∃ α : ℝ, α ≠ 0 ∧ α ≠ dtwin (a θ τ₀) (b θ τ₀) (a' θ τ₀) (b' θ τ₀) τ₀ ∧
        LinearArrival z α τ₀ := by
    intro τ₀ hτ₀ h0
    have hτσ : τ₀ = σ := huniq τ₀ hτ₀ h0
    subst hτσ
    refine ⟨e₂τ θ τ₀ / e₁ θ τ₀, ?_, ?_, linearArrival_of_hasDerivAt hzderiv hz0⟩
    · intro h; rw [h, abs_zero] at hbig; linarith
    · intro h
      have hup := (hrate θ τ₀ hθε₁ (lt_of_lt_of_le hτ₀ hδε₁)).2.2.2
      have hlo := (hrate θ τ₀ hθε₁ (lt_of_lt_of_le hτ₀ hδε₁)).2.2.1
      rw [h, abs_of_pos (by linarith)] at hbig
      linarith
  -- assemble
  obtain ⟨σ', hσ'pos, hσ'le, hσ'lt, hσ'0, huniq', hord, α, ratio, hα, hb, hlim, hratio_eq,
      hratio, hval, hne, htors⟩ :=
    fried_fails_at_crossing_local' (K := K) (V₁ := V₁) (V₂ := V₂) (V₃ := V₃)
      (twin sStar a b θ) (fun τ => dtwin (a θ τ) (b θ τ) (a' θ τ) (b' θ τ) τ) z R c
      (r₀ / 2) δ τR hτR (by positivity) hs0 hsmall' hrateδ hzero hcont hfried_off hexact hacyc
      hdual hdims
  have hσσ' : σ' = σ := huniq σ' (by rw [abs_lt]; constructor <;> linarith) hσ'0
  subst hσσ'
  exact ⟨σ', hσ'pos, hσle', hσ'lt, hσ'0, huniq', hord, hzderiv, hbig, hi, α, ratio, hα, hb, hlim,
    hratio_eq, hratio, hval, hne, htors⟩

end Capstone

end FriedCrossing
