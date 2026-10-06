import SpectralRadiusUpperTail.FlatHaarPrior
import SpectralRadiusUpperTail.ConditionedSubtypeBound
import SpectralRadiusUpperTail.FlatSpectralMatrixWeight
import SpectralRadiusUpperTail.SpectralResidualWeight

namespace SpectralRadiusUpperTail
open MeasureTheory WithLp
open scoped ENNReal
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂]

noncomputable def fullSpectralSphereWeight (n : ℕ) (a : ℝ) (b : 𝕂)
    (x : Fin n → Fin n → 𝕂) : ℝ≥0∞ :=
  ∫⁻ v, ENNReal.ofReal (gaussianMatrixWeight a v
    (spectralTiltTarget b (zeroExtendVector v)) x) ∂haarDirectionLaw 𝕂 n

lemma flatHaar_matrixWeight_le_full (n : ℕ) (L : ℝ) (hL : 1 ≤ L) (hn : 0 < n)
    (hm : (haarDirectionLaw 𝕂 n) (flatUnitDirections 𝕂 n L) ≠ 0)
    (a : ℝ) (b : 𝕂) (x : Fin n → Fin n → 𝕂) :
    flatSpectralMatrixWeight (haarFlatPrior 𝕂 n L hL) a b x ≤
      ((haarDirectionLaw 𝕂 n) (flatUnitDirections 𝕂 n L))⁻¹ *
        fullSpectralSphereWeight n a b x := by
  rw [haarFlatPrior_eq_conditioned 𝕂 n L hL hn hm]
  apply conditionedSubtypeMeasure_lintegral_le _ _ (flatUnitDirections_measurableSet 𝕂 n L)
  unfold gaussianMatrixWeight
  simp only [spectralTiltTarget,zeroExtendVector_fin]
  fun_prop

lemma fullSpectralSphereWeight_eq_sphere (n : ℕ) (a : ℝ) (b : 𝕂)
    (x : Fin n → Fin n → 𝕂) :
    fullSpectralSphereWeight n a b x =
      ∫⁻ v, ENNReal.ofReal (Real.exp (-(n : ℝ)*‖toLp 2
        ((normalizedArray x-b • (1 : Matrix (Fin n) (Fin n) 𝕂)).mulVec (ofLp v.val))‖^2/a))
        ∂haarSphereProbability (volume : Measure (EuclideanSpace 𝕂 (Fin n))) := by
  unfold fullSpectralSphereWeight haarDirectionLaw
  rw [lintegral_map]
  · simp only [gaussianMatrixWeight_spectral]
  · unfold gaussianMatrixWeight
    simp only [spectralTiltTarget,zeroExtendVector_fin]
    fun_prop
  · fun_prop

#print axioms fullSpectralSphereWeight
#print axioms flatHaar_matrixWeight_le_full
#print axioms fullSpectralSphereWeight_eq_sphere
end SpectralRadiusUpperTail
