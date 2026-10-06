import SpectralRadiusUpperTail.MarkedNonrealCodeWeight

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix Matrix.Norms.Operator

theorem markedNonrealCodeWeight_measurable
    (m : ℕ)
    (code : Fin 2 → Fin (Fintype.card (RealSchurMixedCoord (markedNonrealBlockSizes m))) → Bool)
    (g : ℂ → ℝ≥0∞) (hg : Measurable g) :
    Measurable (fun A => markedNonrealCodeWeight m A code g) := by
  classical
  unfold markedNonrealCodeWeight
  apply Finset.measurable_sum
  intro i hi
  have hs : Measurable (fun A => realSchurMixedCanonicalSpectrum (markedNonrealBlockSizes m) A i) :=
    (measurable_pi_apply i).comp (realSchurMixedCanonicalSpectrum_measurable _)
  by_cases hc : code 0 i=true
  · simp only [hc,true_and]
    exact Measurable.ite (measurableSet_lt measurable_const (Complex.continuous_im.measurable.comp hs))
      (hg.comp hs) measurable_const
  · simp only [hc,false_and,ite_false]
    exact measurable_const

theorem markedNonrealBlockWeight_measurable (g : ℂ → ℝ≥0∞) (hg : Measurable g) :
    Measurable (fun B => markedNonrealBlockWeight B g) := by
  have hh : Continuous realPairHeightSq := by
    unfold realPairHeightSq realPairCenter
    fun_prop
  exact Measurable.ite (measurableSet_lt measurable_const hh.measurable)
    (hg.comp realPairUpperRoot_continuous.measurable) measurable_const

theorem markedNonrealCodeWeight_eq_of_charpoly
    (m : ℕ)
    (A B : Matrix (RealSchurMixedCoord (markedNonrealBlockSizes m))
      (RealSchurMixedCoord (markedNonrealBlockSizes m)) ℝ)
    (hA : A.charpoly.Separable) (hB : B.charpoly.Separable) (hpoly : A.charpoly=B.charpoly)
    (code : Fin 2 → Fin (Fintype.card (RealSchurMixedCoord (markedNonrealBlockSizes m))) → Bool)
    (g : ℂ → ℝ≥0∞) : markedNonrealCodeWeight m A code g=markedNonrealCodeWeight m B code g := by
  have hs := realSchurMixedCanonicalSpectrum_eq_of_charpoly _ A B hA hB hpoly
  unfold markedNonrealCodeWeight
  rw [hs]

#print axioms markedNonrealCodeWeight_measurable
#print axioms markedNonrealBlockWeight_measurable
#print axioms markedNonrealCodeWeight_eq_of_charpoly
end SpectralRadiusUpperTail
