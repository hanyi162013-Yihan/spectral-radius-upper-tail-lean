import SpectralRadiusUpperTail.RealSchurNativeSpectralCoordinates
import SpectralRadiusUpperTail.RealPairSpectralGapMeasure

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix

noncomputable def realSchurNativeAtomicEntrySet (q : ℕ) : Set ((Fin q × Fin q) → ℝ) :=
  {A | q ≠ 2 ∨ 0 < (realSchurNativeSpectralCoordinates q A).2.1}

theorem measurableSet_realSchurNativeAtomicEntrySet (q : ℕ) :
    MeasurableSet (realSchurNativeAtomicEntrySet q) := by
  by_cases hq : q=2
  · have he : realSchurNativeAtomicEntrySet q =
        {A | 0 < (realSchurNativeSpectralCoordinates q A).2.1} := by
      ext A
      simp [realSchurNativeAtomicEntrySet,hq]
    rw [he]
    exact measurableSet_lt measurable_const (realSchurNativeSpectralCoordinates_measurable q).snd.fst
  · have he : realSchurNativeAtomicEntrySet q=Set.univ := by
      ext A
      simp [realSchurNativeAtomicEntrySet,hq]
    rw [he]
    exact MeasurableSet.univ

theorem realSchurNativeAtomicEntrySet_two :
    realSchurNativeAtomicEntrySet 2=realPairNonrealEntrySet := by
  ext A
  simp [realSchurNativeAtomicEntrySet,realSchurNativeSpectralCoordinates_two,
    realPairSpectralGapCoordinates,realPairNonrealEntrySet]

theorem realSchurNativeAtomicEntrySet_one : realSchurNativeAtomicEntrySet 1=Set.univ := by
  ext A
  simp [realSchurNativeAtomicEntrySet]

theorem realSchurNativeAtomicEntrySet_of_noRealRoot (q : ℕ) (A : (Fin q × Fin q) → ℝ)
    (h : q=2 → ∀ x : ℝ, (Matrix.of A.curry).charpoly.eval x ≠ 0) :
    A ∈ realSchurNativeAtomicEntrySet q := by
  by_cases hq : q=2
  · subst q
    rw [realSchurNativeAtomicEntrySet_two]
    exact (realPair_noRealRoot_iff (Matrix.of A.curry)).mp (h rfl)
  · exact Or.inl hq

noncomputable def realSchurNativeGaussianMeasure (q : ℕ) (n : ℝ) : Measure ((Fin q × Fin q) → ℝ) :=
  (realArrayGaussianMeasure n).restrict (realSchurNativeAtomicEntrySet q)

noncomputable def realSchurNativeSpectralMeasure (q : ℕ) (n : ℝ) : Measure (ℝ × (ℝ × ℝ)) :=
  (realSchurNativeGaussianMeasure q n).map (realSchurNativeSpectralCoordinates q)

theorem realSchurNativeGaussianMeasure_finite (q : ℕ) (n : ℝ) (hn : 0 < n) :
    IsFiniteMeasure (realSchurNativeGaussianMeasure q n) := by
  let := realArrayGaussianMeasure_finite (ι := Fin q × Fin q) n hn
  unfold realSchurNativeGaussianMeasure
  infer_instance

theorem realSchurNativeSpectralMeasure_finite (q : ℕ) (n : ℝ) (hn : 0 < n) :
    IsFiniteMeasure (realSchurNativeSpectralMeasure q n) := by
  let := realSchurNativeGaussianMeasure_finite q n hn
  unfold realSchurNativeSpectralMeasure
  infer_instance

theorem realSchurNativeGaussianMeasure_two (n : ℝ) :
    realSchurNativeGaussianMeasure 2 n=realPairGaussianNonrealMeasure n := by
  simp only [realSchurNativeGaussianMeasure,realSchurNativeAtomicEntrySet_two,
    realPairGaussianNonrealMeasure]

theorem realSchurNativeSpectralMeasure_two (n : ℝ) :
    realSchurNativeSpectralMeasure 2 n=realPairSpectralGapMeasure n := by
  unfold realSchurNativeSpectralMeasure realPairSpectralGapMeasure
  rw [realSchurNativeGaussianMeasure_two]
  congr 1

#print axioms measurableSet_realSchurNativeAtomicEntrySet
#print axioms realSchurNativeAtomicEntrySet_of_noRealRoot
#print axioms realSchurNativeGaussianMeasure_finite
#print axioms realSchurNativeSpectralMeasure_finite
#print axioms realSchurNativeSpectralMeasure_two
end SpectralRadiusUpperTail
