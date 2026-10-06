import SpectralRadiusUpperTail.ActualMatrixIdentity
import Mathlib.Tactic.NoncommRing

namespace SpectralRadiusUpperTail
open MeasureTheory
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂] {N : ℕ}

/-- Exact error relative to the iid triangular comparator plus its deterministic mean. -/
lemma gaussianMatrix_approximation_error (μ : Measure 𝕂) (a : ℝ) (v : ℕ → 𝕂)
    (t : Fin N → 𝕂) (η : ℝ) (hη : 0 < η) (x z : Fin N → Fin N → 𝕂) :
    normalizedArray x -
      (normalizedArray z * descendingTriangularInverse η (fun j : Fin N => v j.val) +
        gaussianMeanMatrix v t η) =
      (gaussianCenteredMatrix μ a v t x z + gaussianRegressionMatrix μ a v t η x) *
        descendingTriangularInverse η (fun j : Fin N => v j.val) := by
  rw [gaussianMatrix_triangular_identity μ a v t η hη x z]
  noncomm_ring

#print axioms gaussianMatrix_approximation_error
end SpectralRadiusUpperTail
