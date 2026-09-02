/-
THE CAPSTONE (8/31, per Ben: "it's clearly identified in the lean project how all
the pieces fit together?") — one theorem that COMPOSES the suite, so that its
hypothesis list IS the program's input ledger and one `#print axioms` audits the
whole chain. ⚡AUDIT CRITERION: Lean built-ins only.

THE WIRING (hypothesis → citation → where it gets discharged):
  `hconst` — BL Theorem 6.7.1 (generalized metric b-independent; §6.4 truncation)
             [citation; M1 read DONE 8/25–27]
  `h0`     — BL Theorem 8.2.1 at b → 0⁺, corrections vanishing for acyclic ρ on
             odd-dim X [citation; M1 read DONE; residue = hbundle, §1.1–1.2 photo]
  `hrepr`  — definition of the spectral reading (graded/supertrace objects — the
             8/28 falsifier's finding 1)
  `hl,hm`  — trace-class summability [V1/V2-grade bookkeeping]
  `hpt`    — per-resonance convergence [Drouot stochastic stability; twisted flag;
             read #3]
  `htail`  — uniform tail smallness at fixed cuts [hdom — THE one owed estimate;
             route: hdom_route_8_27]
  `hread`  — the torsion quantity is read as the spectral trace at large b
             [V2, flat-trace/trace-formula citation]
  conclusion: T = (transport reading).re — torsion equals the zeta-side value:
             FRIED, in the abstract shape the note instantiates.

THE OTHER TWO LAYERS (separate sockets, by design not composed here):
  route-ii files    — [uniform gap ⇒ endpoint strip]: consumes Drouot-attainment +
                      the gap; makes H's clause structure collapse.
  h_mixing file     — [endpoint mixing ⇒ uniform gap]: `uniform_gap_of_block_mixing`
                      with `hmix` = stage-1 transfer × stage-2 mixing (Front Page ¶5;
                      stage2_paper_program_8_31). H itself enters THIS capstone only
                      through the citations that consume it (htail's b-tracking and
                      hpt/hread's endpoint inputs), matching the note's ledger.
-/
import Mathlib
import B1s.endpoints_8_20

set_option linter.style.header false

namespace FriedCapstone

open Filter Topology

/-- FRIED FROM THE INPUT LEDGER: constancy (BL 6.7.1) + the b → 0 torsion limit
(BL 8.2.1) + the spectral reading's convergence machinery (hpt = Drouot,
htail = hdom, summability bookkeeping) + the large-b identification (V2) force
torsion = the transport/zeta reading. Every hypothesis is one ledger line; see the
file header for the wiring map. -/
theorem fried_of_inputs
    (f : ℝ → ℝ) (c T : ℝ) (F : ℝ → ℂ) (lam : ℝ → ℕ → ℂ) (mu : ℕ → ℂ) (ℓ : ℕ)
    (hconst : ∀ b ∈ Set.Ioi (0 : ℝ), f b = c)
    (h0 : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 T))
    (hrepr : ∀ b, F b = ∑' i, lam b i ^ ℓ)
    (hl : ∀ b, Summable fun i => ‖lam b i‖ ^ ℓ)
    (hm : Summable fun i => ‖mu i‖ ^ ℓ)
    (hpt : ∀ i, Tendsto (fun b => lam b i) atTop (𝓝 (mu i)))
    (htail : ∀ ε > 0, ∃ N₀ : ℕ, ∀ᶠ b in atTop,
      (∑' i, ‖lam b (i + N₀)‖ ^ ℓ) ≤ ε)
    (hread : ∀ᶠ b in atTop, f b = (F b).re) :
    T = (∑' i, mu i ^ ℓ).re := by
  have hF := FriedEndpoints.v5_limit_assembly_ofPointwise F lam mu ℓ
    hrepr hl hm hpt htail
  have hFre : Tendsto (fun b => (F b).re) atTop (𝓝 ((∑' i, mu i ^ ℓ).re)) :=
    (Complex.continuous_re.tendsto _).comp hF
  have hinf : Tendsto f atTop (𝓝 ((∑' i, mu i ^ ℓ).re)) :=
    Tendsto.congr' (hread.mono fun b hb => hb.symm) hFre
  exact FriedEndpoints.endpointGlue f c T _ hconst h0 hinf

end FriedCapstone
