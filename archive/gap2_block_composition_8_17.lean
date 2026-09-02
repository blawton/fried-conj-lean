/-
GAP-2 BLOCK-COMPOSITION SPINE (8/17) — the comparison lemma's skeleton, obligation
1-BRIDGE of note_preflight_8_15.md. Companion: gap2_comparison_lemma_8_17.md (statement,
proof route, window analysis), gap2_block_window_test_8_17.py (mechanism test).

GAP 2 = transfer per-unit-time decay from AUTONOMOUS frozen SM members (where the
hypothesis H lives) to the radially-CONDITIONED kinetic process (what the bridge uses).
Route: block the time axis at scale L; per block the conditioned propagator S_j is
adiabatically close to the frozen propagator F_j of the SM member at the block's mean
radius; H (via a uniform renormed/hypocoercive norm) makes each F_j a strict contraction
at rate γ_j·L. This file machine-checks the COMPOSITION algebra of that route — the
part that is pure normed-algebra bookkeeping — with zero axioms:

  normProdLeOne       — products of contractions are contractions.
  blockContraction    — per-block rates compose: ‖∏F_j‖ ≤ exp(−Σ γ_j L).
  adiabaticTelescope  — the product-difference bound ‖∏S − ∏F‖ ≤ Σ‖S_j − F_j‖
                        (all factors contractions): the total adiabatic error is the
                        SUM of per-block errors — no compounding.
  gap2Spine           — the assembled comparison bound:
                        ‖∏S‖ ≤ exp(−Σ γ_j L) + Σ δ_j.

Cited-hypothesis slots (analytic inputs, NOT proven here — see companion note):
  (H-FROZEN)  each frozen member contracts at rate γ(b_eff) in a norm uniformly
              equivalent to L² — supplied by H + semigroup renorming; uniformity of the
              equivalence constant C over the swept b_eff range is the norm-switching
              cost log C per block.
  (ADIABATIC) ‖S_j − F_j‖ ≤ δ_j with δ_j controlled by the radial oscillation on the
              block (Duhamel + generator Lipschitz in r); E[Σδ_j] small iff L ≪ b².
  Window: the route closes iff log C/β ≪ L ≪ b² — nonempty exactly in the large-b
  regime the budget consumes; small-b remainder absorbed by the budgeted e^{cb²}
  prefactors (budget_davies_prefactor_check_8_15).
-/
import Mathlib

namespace FriedGap2Block

variable {A : Type*} [NormedRing A] [NormOneClass A]

/-- Products of contractions are contractions. -/
theorem normProdLeOne : ∀ (l : List A), (∀ x ∈ l, ‖x‖ ≤ 1) → ‖l.prod‖ ≤ 1
  | [], _ => by simp
  | x :: xs, h => by
    have hx : ‖x‖ ≤ 1 := h x (by simp)
    have ih : ‖xs.prod‖ ≤ 1 :=
      normProdLeOne xs fun y hy => h y (by simp [hy])
    calc ‖(x :: xs).prod‖ = ‖x * xs.prod‖ := by rw [List.prod_cons]
      _ ≤ ‖x‖ * ‖xs.prod‖ := norm_mul_le _ _
      _ ≤ 1 * 1 := mul_le_mul hx ih (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1

/-- Per-block rates compose across blocks: pairs (F_j, g_j) with ‖F_j‖ ≤ exp(−g_j)
give ‖∏F_j‖ ≤ exp(−Σg_j). (g_j = γ(b_eff(r̄_j))·L in the application.) -/
theorem blockContraction : ∀ (p : List (A × ℝ)),
    (∀ q ∈ p, ‖q.1‖ ≤ Real.exp (-q.2)) →
    ‖(p.map Prod.fst).prod‖ ≤ Real.exp (-(p.map Prod.snd).sum)
  | [], _ => by simp
  | q :: ps, h => by
    have hq : ‖q.1‖ ≤ Real.exp (-q.2) := h q (by simp)
    have ih := blockContraction ps fun w hw => h w (by simp [hw])
    calc ‖((q :: ps).map Prod.fst).prod‖
        = ‖q.1 * (ps.map Prod.fst).prod‖ := by simp
      _ ≤ ‖q.1‖ * ‖(ps.map Prod.fst).prod‖ := norm_mul_le _ _
      _ ≤ Real.exp (-q.2) * Real.exp (-(ps.map Prod.snd).sum) :=
          mul_le_mul hq ih (norm_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (-((q :: ps).map Prod.snd).sum) := by
          rw [← Real.exp_add]; congr 1; simp; ring

/-- Adiabatic telescope: for two equal-length lists of contractions, the product
difference is bounded by the SUM of factor differences — per-block errors add, they do
not compound. This is the entire adiabatic bookkeeping of the block route. -/
theorem adiabaticTelescope : ∀ (s f : List A), s.length = f.length →
    (∀ x ∈ s, ‖x‖ ≤ 1) → (∀ x ∈ f, ‖x‖ ≤ 1) →
    ‖s.prod - f.prod‖ ≤ (List.zipWith (fun x y => ‖x - y‖) s f).sum
  | [], [], _, _, _ => by simp
  | [], _ :: _, h, _, _ => by simp at h
  | _ :: _, [], h, _, _ => by simp at h
  | x :: xs, y :: ys, h, hs, hf => by
    have hlen : xs.length = ys.length := by simpa using h
    have hx : ‖x‖ ≤ 1 := hs x (by simp)
    have hys : ‖ys.prod‖ ≤ 1 := normProdLeOne ys fun z hz => hf z (by simp [hz])
    have ih := adiabaticTelescope xs ys hlen
      (fun z hz => hs z (by simp [hz])) (fun z hz => hf z (by simp [hz]))
    have key : (x :: xs).prod - (y :: ys).prod
        = x * (xs.prod - ys.prod) + (x - y) * ys.prod := by
      simp only [List.prod_cons]; noncomm_ring
    calc ‖(x :: xs).prod - (y :: ys).prod‖
        = ‖x * (xs.prod - ys.prod) + (x - y) * ys.prod‖ := by rw [key]
      _ ≤ ‖x * (xs.prod - ys.prod)‖ + ‖(x - y) * ys.prod‖ := norm_add_le _ _
      _ ≤ ‖x‖ * ‖xs.prod - ys.prod‖ + ‖x - y‖ * ‖ys.prod‖ :=
          add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ 1 * (List.zipWith (fun a b => ‖a - b‖) xs ys).sum + ‖x - y‖ * 1 :=
          add_le_add (mul_le_mul hx ih (norm_nonneg _) zero_le_one)
            (mul_le_mul_of_nonneg_left hys (norm_nonneg _))
      _ = ‖x - y‖ + (List.zipWith (fun a b => ‖a - b‖) xs ys).sum := by ring
      _ = (List.zipWith (fun a b => ‖a - b‖) (x :: xs) (y :: ys)).sum := by simp

/-- THE GAP-2 SPINE, assembled: true blocks S_j (contractions), frozen reference blocks
F_j with rates g_j (from H-FROZEN), per-block adiabatic errors ‖S_j − F_j‖ (from
ADIABATIC) ⇒ the conditioned propagator obeys the composed frozen rate up to the summed
adiabatic error. -/
theorem gap2Spine (s : List A) (p : List (A × ℝ))
    (hlen : s.length = p.length)
    (hs : ∀ x ∈ s, ‖x‖ ≤ 1)
    (hf1 : ∀ q ∈ p, ‖q.1‖ ≤ 1)
    (hf2 : ∀ q ∈ p, ‖q.1‖ ≤ Real.exp (-q.2)) :
    ‖s.prod‖ ≤ Real.exp (-(p.map Prod.snd).sum)
      + (List.zipWith (fun x y => ‖x - y‖) s (p.map Prod.fst)).sum := by
  have hlen' : s.length = (p.map Prod.fst).length := by simpa using hlen
  have hf1' : ∀ x ∈ p.map Prod.fst, ‖x‖ ≤ 1 := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
    exact hf1 q hq
  have tri : ‖s.prod‖ ≤ ‖s.prod - (p.map Prod.fst).prod‖ + ‖(p.map Prod.fst).prod‖ := by
    calc ‖s.prod‖ = ‖(s.prod - (p.map Prod.fst).prod) + (p.map Prod.fst).prod‖ := by
          rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  calc ‖s.prod‖
      ≤ ‖s.prod - (p.map Prod.fst).prod‖ + ‖(p.map Prod.fst).prod‖ := tri
    _ ≤ (List.zipWith (fun x y => ‖x - y‖) s (p.map Prod.fst)).sum
        + Real.exp (-(p.map Prod.snd).sum) :=
        add_le_add (adiabaticTelescope s (p.map Prod.fst) hlen' hs hf1')
          (blockContraction p hf2)
    _ = _ := by ring

end FriedGap2Block
