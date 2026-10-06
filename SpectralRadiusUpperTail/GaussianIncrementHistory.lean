import SpectralRadiusUpperTail.ActualRegressionIdentity
import SpectralRadiusUpperTail.GaussianSequentialCentering

namespace SpectralRadiusUpperTail
open MeasureTheory
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂] {N : ℕ}

/-- Actual paired history stored before the descending coordinate j is revealed. -/
def upperPairedHistory (j : Fin N) (x : Fin N → 𝕂 × 𝕂) : Fin (N-(j.val+1)) → 𝕂 × 𝕂 :=
  fun i => x ⟨j.val+1+i.val, by omega⟩

lemma upperPairedHistory_source (j : Fin N) (x : Fin N → 𝕂 × 𝕂) :
    coordinateVector Prod.fst (N-(j.val+1)) (upperPairedHistory j x) =
      upperRowHistory j (coordinateVector Prod.fst N x) := rfl

/-- The centered error used in the full triangular matrix equation is exactly
the increment centered by the actual sequential transition kernel. -/
theorem gaussianSequentialIncrement_eq_row_increment (μ : Measure 𝕂) (v : ℕ → 𝕂)
    (a : ℝ) (t : 𝕂) (j : Fin N) (x : Fin N → 𝕂 × 𝕂) :
    gaussianSequentialIncrement μ v a N t (N-(j.val+1)) (upperPairedHistory j x, x j) =
      gaussianRowCenteredIncrement μ a v j t (coordinateVector Prod.fst N x)
        (comparatorVector N x) := by
  have hj : N-(N-(j.val+1)+1) = j.val := by omega
  unfold gaussianSequentialIncrement gaussianRowCenteredIncrement
  rw [hj, upperPairedHistory_source, upperRowHistory_revealedSum]
  rfl

#print axioms gaussianSequentialIncrement_eq_row_increment
end SpectralRadiusUpperTail
