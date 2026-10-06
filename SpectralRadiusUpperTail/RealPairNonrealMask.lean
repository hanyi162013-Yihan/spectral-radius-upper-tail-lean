import SpectralRadiusUpperTail.RealPairOrbitIntegral
import SpectralRadiusUpperTail.RealSchurMixedChartSpectrum

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix

def realPairNonrealEntrySet : Set ((Fin 2 × Fin 2) → ℝ) :=
  {A | 0 < realPairHeightSq (Matrix.of A.curry)}

theorem measurableSet_realPairNonrealEntrySet : MeasurableSet realPairNonrealEntrySet := by
  apply isOpen_lt continuous_const _ |>.measurableSet
  unfold realPairHeightSq realPairCenter
  simp only [Matrix.trace_fin_two,Matrix.det_fin_two]
  change Continuous (fun A : (Fin 2 × Fin 2) → ℝ =>
    A (0,0)*A (1,1)-A (0,1)*A (1,0)-((A (0,0)+A (1,1))/2)^2)
  fun_prop

theorem realPairNonrealEntrySet_conjugation
    (Q A : Matrix (Fin 2) (Fin 2) ℝ) (hQ : Qᵀ*Q=1) :
    (fun ij => (Q*A*Qᵀ) ij.1 ij.2) ∈ realPairNonrealEntrySet ↔
      (fun ij => A ij.1 ij.2) ∈ realPairNonrealEntrySet := by
  change 0 < realPairHeightSq (Q*A*Qᵀ) ↔ 0 < realPairHeightSq A
  rw [← realPair_noRealRoot_iff,← realPair_noRealRoot_iff,
    realMatrixOrthogonalConjugation_charpoly _ Q A hQ]

theorem realPairNonrealEntrySet_block (x q r : ℝ) :
    (fun ij => realSchurBlock x (q+r) (q-r) ij.1 ij.2) ∈ realPairNonrealEntrySet ↔ r^2 < q^2 := by
  have he : realPairHeightSq (realSchurBlock x (q+r) (q-r))=q^2-r^2 := by
    unfold realPairHeightSq realPairCenter
    simp [realSchurBlock,Matrix.trace_fin_two,Matrix.det_fin_two]
    ring
  change 0 < realPairHeightSq (realSchurBlock x (q+r) (q-r)) ↔ _
  rw [he,sub_pos]

theorem RealPairOrthogonalInvariant.nonreal_mask
    (g : ((Fin 2 × Fin 2) → ℝ) → ℝ≥0∞) (h : RealPairOrthogonalInvariant g) :
    RealPairOrthogonalInvariant (realPairNonrealEntrySet.indicator g) := by
  classical
  intro Q hQ A
  simp only [Set.indicator_apply,realPairNonrealEntrySet_conjugation Q A hQ,h Q hQ A]

#print axioms measurableSet_realPairNonrealEntrySet
#print axioms realPairNonrealEntrySet_conjugation
#print axioms realPairNonrealEntrySet_block
#print axioms RealPairOrthogonalInvariant.nonreal_mask
end SpectralRadiusUpperTail
