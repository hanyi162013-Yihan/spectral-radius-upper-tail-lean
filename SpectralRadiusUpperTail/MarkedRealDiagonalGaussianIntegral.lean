import SpectralRadiusUpperTail.MarkedRealDiagonalGaussianEnergy
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Classical
open scoped ENNReal Matrix BigOperators

theorem markedRealSimpleDiagonalWeight_measurable
    (m : ℕ) (hm : 0 < m) (b : ℝ) :
    Measurable (markedRealSimpleDiagonalWeight m b) := by
  have h : Measurable
      (fun d : RealSchurMixedDiagonalEntry
        (markedRealTwoBlockSizes m) → ℝ =>
        ∑' k : ℕ, markedRealRankDiagonalWeight m k b d) :=
    Measurable.tsum
      (fun k : ℕ => markedRealRankDiagonalWeight_measurable m k hm b)
  convert h using 1
  funext d
  exact (markedRealRankDiagonalWeight_tsum m b d).symm

/-- The remaining diagonal Gaussian integral lives on one scalar and
one complementary matrix, with no change-of-variables factor. -/
theorem markedRealSimpleDiagonalWeight_lintegral_product
    (m : ℕ) (hm : 0 < m) (b : ℝ) :
    (∫⁻ d, markedRealSimpleDiagonalWeight m b d) =
      ∫⁻ z : ℝ × ((Fin m × Fin m) → ℝ),
        markedRealSimpleDiagonalWeight m b
          ((markedRealDiagonalProductEquiv m).symm z) := by
  let E := markedRealDiagonalProductEquiv m
  have hE : MeasurePreserving E :=
    markedRealDiagonalProductEquiv_measurePreserving m
  have hf : Measurable (fun z : ℝ × ((Fin m × Fin m) → ℝ) =>
      markedRealSimpleDiagonalWeight m b (E.symm z)) :=
    (markedRealSimpleDiagonalWeight_measurable m hm b).comp
      E.symm.measurable
  have h :
      (∫⁻ d, markedRealSimpleDiagonalWeight m b (E.symm (E d))) =
        ∫⁻ z, markedRealSimpleDiagonalWeight m b (E.symm z) :=
    hE.lintegral_comp hf
  calc
    (∫⁻ d, markedRealSimpleDiagonalWeight m b d) =
        ∫⁻ d, markedRealSimpleDiagonalWeight m b (E.symm (E d)) := by
      apply lintegral_congr_ae
      exact Filter.Eventually.of_forall (fun d => by
        change markedRealSimpleDiagonalWeight m b d =
          markedRealSimpleDiagonalWeight m b (E.symm (E d))
        exact congrArg (markedRealSimpleDiagonalWeight m b)
          (E.symm_apply_apply d).symm)
    _ = _ := h

#print axioms markedRealSimpleDiagonalWeight_measurable
#print axioms markedRealSimpleDiagonalWeight_lintegral_product
end SpectralRadiusUpperTail
