import SpectralRadiusUpperTail.RealPairGaussianGapIntegral
import SpectralRadiusUpperTail.RealPairUpperRoot
import SpectralRadiusUpperTail.GinibrePoissonSharp
import SpectralRadiusUpperTail.RealSchurMixedGaussianUpperLIntegral
import Mathlib.MeasureTheory.Measure.OpenPos

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix

noncomputable def markedNonrealPairTestIntegral (m : ℕ) (g : ℂ → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ B in realPairNonrealEntrySet, realPairGaussianWeight 1 B*
    (ENNReal.ofReal (ginibreExpPartial (m+1)
      ((realPairCenter (Matrix.of B.curry))^2+realPairHeightSq (Matrix.of B.curry)))*
        g (realPairUpperRoot (Matrix.of B.curry)))

noncomputable def markedNonrealPairReferenceMass : ℝ≥0∞ :=
  ∫⁻ B in realPairNonrealEntrySet, realPairGaussianWeight 1 B

theorem realPairNonrealEntrySet_isOpen : IsOpen realPairNonrealEntrySet := by
  apply isOpen_lt continuous_const
  unfold realPairHeightSq realPairCenter
  simp only [Matrix.trace_fin_two,Matrix.det_fin_two]
  change Continuous (fun A : (Fin 2 × Fin 2) → ℝ =>
    A (0,0)*A (1,1)-A (0,1)*A (1,0)-((A (0,0)+A (1,1))/2)^2)
  fun_prop

theorem markedNonrealPairReferenceMass_pos : 0 < markedNonrealPairReferenceMass := by
  have hn : realPairNonrealEntrySet.Nonempty := by
    refine ⟨fun p => realSchurBlock 0 1 1 p.1 p.2,?_⟩
    norm_num [realPairNonrealEntrySet,realPairHeightSq,realPairCenter,
      realSchurBlock,Matrix.trace_fin_two,Matrix.det_fin_two]
  have hp := realPairNonrealEntrySet_isOpen.measure_pos volume hn
  have hs : Function.support (realPairGaussianWeight 1)=Set.univ := by
    ext B
    simp only [Function.mem_support,Set.mem_univ,iff_true]
    exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  unfold markedNonrealPairReferenceMass
  rw [setLIntegral_pos_iff (realPairGaussianWeight_measurable 1),hs,Set.univ_inter]
  exact hp

theorem markedNonrealPairReferenceMass_ne_top : markedNonrealPairReferenceMass ≠ ∞ := by
  have hle : markedNonrealPairReferenceMass ≤
      ∫⁻ B : (Fin 2 × Fin 2) → ℝ, realPairGaussianWeight 1 B :=
    setLIntegral_le_lintegral _ _
  have he (B : (Fin 2 × Fin 2) → ℝ) : realPairGaussianWeight 1 B=
      ENNReal.ofReal (Real.exp (-(∑ p, (B p)^2)/2)) := by
    unfold realPairGaussianWeight
    congr 2
    ring
  simp_rw [he] at hle
  rw [realSchurMixedIndependentGaussianLIntegral] at hle
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle

theorem ginibreExpPartial_succ_ge_one (m : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    1 ≤ ginibreExpPartial (m+1) x := by
  have h := Finset.single_le_sum
    (fun k (_hk : k ∈ Finset.range (m+1)) =>
      div_nonneg (pow_nonneg hx k) (by positivity : (0 : ℝ) ≤ k.factorial))
    (show 0 ∈ Finset.range (m+1) by simp)
  simpa only [ginibreExpPartial,pow_zero,Nat.factorial_zero,Nat.cast_one,div_one] using h

/-- The reference mass is fixed and positive, independently of the
complementary dimension. It will calibrate the unknown angular constant. -/
theorem markedNonrealPairReferenceMass_le_testIntegral (m : ℕ) :
    markedNonrealPairReferenceMass ≤ markedNonrealPairTestIntegral m (fun _ => 1) := by
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_realPairNonrealEntrySet] with B hB
  change realPairGaussianWeight 1 B ≤ realPairGaussianWeight 1 B*(_*1)
  rw [mul_one]
  have hx : 0 ≤ (realPairCenter (Matrix.of B.curry))^2+realPairHeightSq (Matrix.of B.curry) :=
    add_nonneg (sq_nonneg _) hB.le
  have h := ENNReal.ofReal_le_ofReal (ginibreExpPartial_succ_ge_one m _ hx)
  rw [ENNReal.ofReal_one] at h
  exact le_mul_of_one_le_right' h

#print axioms realPairNonrealEntrySet_isOpen
#print axioms markedNonrealPairReferenceMass_pos
#print axioms markedNonrealPairReferenceMass_ne_top
#print axioms ginibreExpPartial_succ_ge_one
#print axioms markedNonrealPairReferenceMass_le_testIntegral
end SpectralRadiusUpperTail
