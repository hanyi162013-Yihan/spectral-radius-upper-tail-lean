import SpectralRadiusUpperTail.GaussianStoppedRow

namespace SpectralRadiusUpperTail
open MeasureTheory
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂]

/-- The terminal target is exactly the target used by its actual history kernel. -/
lemma gaussianTerminalTarget_eq_history (v : ℕ → 𝕂) (N : ℕ) (t : 𝕂) (n : ℕ)
    (hn : n ≤ N) (x : Fin N → 𝕂 × 𝕂) :
    gaussianTerminalTarget v N t n x =
      t-revealedSum (fun i z => v i*z) N n
        (coordinateVector Prod.fst n (pathSuffix N n hn x)) := by
  unfold gaussianTerminalTarget
  rw [terminalRevealedSum_of_le _ N n hn]
  rfl

lemma gaussianSafeHistory_target_bound (v : ℕ → 𝕂) (N : ℕ) (t : 𝕂)
    (n : ℕ) (hn : n ≤ N) (K : ℝ) (x : Fin N → 𝕂 × 𝕂)
    (hx : x ∈ prefixSafeEvent (gaussianTerminalTarget v N t) K n) :
    ‖t-revealedSum (fun i z => v i*z) N n
      (coordinateVector Prod.fst n (pathSuffix N n hn x))‖ ≤ K := by
  rw [← gaussianTerminalTarget_eq_history v N t n hn x]
  exact prefixSafeEvent_mem_current _ _ _ hx

#print axioms gaussianSafeHistory_target_bound
end SpectralRadiusUpperTail
