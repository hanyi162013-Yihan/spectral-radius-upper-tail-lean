import SpectralRadiusUpperTail.MarkedNonrealRootCodeSum
import SpectralRadiusUpperTail.MarkedNonrealWeightMeasurable
import SpectralRadiusUpperTail.MarkedNonrealFlagAtlas

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix Matrix.Norms.Operator

noncomputable def markedNonrealRootWeight (m : ℕ) (A : Matrix (MarkedNonrealIndex m) (MarkedNonrealIndex m) ℝ)
    (g : ℂ → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ i, if 0 < (realSchurMixedCanonicalSpectrum (markedNonrealBlockSizes m) A i).im then
    g (realSchurMixedCanonicalSpectrum (markedNonrealBlockSizes m) A i) else 0

theorem markedNonrealRootWeight_measurable (m : ℕ) (g : ℂ → ℝ≥0∞) (hg : Measurable g) :
    Measurable (fun A => markedNonrealRootWeight m A g) := by
  unfold markedNonrealRootWeight
  apply Finset.measurable_sum
  intro i hi
  have hs : Measurable (fun A => realSchurMixedCanonicalSpectrum (markedNonrealBlockSizes m) A i) :=
    (measurable_pi_apply i).comp (realSchurMixedCanonicalSpectrum_measurable _)
  exact Measurable.ite (measurableSet_lt measurable_const (Complex.continuous_im.measurable.comp hs))
    (hg.comp hs) measurable_const

theorem markedNonrealRootWeight_one_le (m : ℕ)
    (A : Matrix (MarkedNonrealIndex m) (MarkedNonrealIndex m) ℝ) :
    markedNonrealRootWeight m A (fun _ => 1) ≤ (m+2 : ℕ) := by
  classical
  unfold markedNonrealRootWeight
  calc
    _ ≤ ∑ _i : Fin (Fintype.card (MarkedNonrealIndex m)), (1 : ℝ≥0∞) := by
      apply Finset.sum_le_sum
      intro i hi
      split_ifs
      · exact le_rfl
      · exact zero_le
    _ = _ := by simp [MarkedNonrealIndex,markedNonrealCoord_card,add_comm]

#print axioms markedNonrealRootWeight_measurable
#print axioms markedNonrealRootWeight_one_le
end SpectralRadiusUpperTail
