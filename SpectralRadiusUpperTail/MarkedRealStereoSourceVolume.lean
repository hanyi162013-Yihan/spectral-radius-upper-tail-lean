import SpectralRadiusUpperTail.MarkedRealStereoAngularJacobian
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

namespace SpectralRadiusUpperTail
open MeasureTheory Set Classical
open scoped Matrix BigOperators ENNReal

theorem markedRealStereoSource_eq_sum_squares (m : ℕ) :
    markedRealStereoSource m =
      {w : RealSchurMixedOrbitIndex (markedRealTwoBlockSizes m) → ℝ |
        ∑ i, (w i)^2 < 1} := by
  ext w
  have he := (markedRealOrbitEquiv m).sum_comp (fun i => (w i)^2)
  change (∑ i : Fin m, w (markedRealOrbitEquiv m i)*w (markedRealOrbitEquiv m i)) < 1 ↔ _
  simp only [← pow_two, he, Set.mem_setOf_eq]

theorem isOpen_markedRealStereoSource (m : ℕ) :
    IsOpen (markedRealStereoSource m) := by
  rw [markedRealStereoSource_eq_sum_squares]
  apply isOpen_lt _ continuous_const
  fun_prop

/-- The parameter hemisphere has the exact volume of an m-dimensional
Euclidean unit ball, in the project's existing coordinate volume. -/
theorem volume_markedRealStereoSource (m : ℕ) :
    (volume : Measure (RealSchurMixedOrbitIndex (markedRealTwoBlockSizes m) → ℝ))
      (markedRealStereoSource m) =
      ENNReal.ofReal ((Real.sqrt Real.pi)^m/Real.Gamma ((m : ℝ)/2+1)) := by
  have hc : Fintype.card (RealSchurMixedOrbitIndex (markedRealTwoBlockSizes m)) = m := by
    simpa using (Fintype.card_congr (markedRealOrbitEquiv m)).symm
  have hG : 2*Real.Gamma ((1 : ℝ)/2+1) = Real.sqrt Real.pi := by
    rw [Real.Gamma_add_one (by norm_num : (1 : ℝ)/2 ≠ 0), Real.Gamma_one_half_eq]
    ring
  have hh := volume_sum_rpow_lt_one
    (RealSchurMixedOrbitIndex (markedRealTwoBlockSizes m)) (p := 2) (by norm_num)
  rw [markedRealStereoSource_eq_sum_squares]
  simpa only [Real.rpow_two, sq_abs, hc, hG] using hh

noncomputable def markedRealStereoAngularWeight (m : ℕ)
    (w : RealSchurMixedOrbitIndex (markedRealTwoBlockSizes m) → ℝ) : ℝ≥0∞ :=
  if w ∈ markedRealStereoSource m then
    ENNReal.ofReal |markedRealStereoAngularJacobian m w| else 0


theorem markedRealStereoAngularWeight_measurable (m : ℕ) :
    Measurable (markedRealStereoAngularWeight m) := by
  unfold markedRealStereoAngularWeight
  simp only [markedRealStereoAngularJacobian_abs]
  apply Measurable.ite (isOpen_markedRealStereoSource m).measurableSet _ measurable_const
  have hd : Continuous (fun w =>
      markedRealStereoDenom m (markedRealStereoParameterCLM m w)) :=
    (markedRealStereoDenom_contDiff m).continuous.comp
      (markedRealStereoParameterCLM m).continuous
  exact ((continuous_const.div hd (fun w =>
    (markedRealStereoDenom_pos m _).ne')).pow m).measurable.ennreal_ofReal

theorem markedRealStereoAngularWeight_ge_one (m : ℕ)
    (w : RealSchurMixedOrbitIndex (markedRealTwoBlockSizes m) → ℝ)
    (hw : w ∈ markedRealStereoSource m) :
    1 ≤ markedRealStereoAngularWeight m w := by
  rw [markedRealStereoAngularWeight, if_pos hw, markedRealStereoAngularJacobian_abs]
  have hc : 1 ≤ 2/markedRealStereoDenom m (markedRealStereoParameterCLM m w) := by
    apply (le_div_iff₀ (markedRealStereoDenom_pos m _)).mpr
    change 1*(1+markedRealStereoParameterCLM m w ⬝ᵥ markedRealStereoParameterCLM m w) ≤ 2
    change markedRealStereoParameterCLM m w ⬝ᵥ markedRealStereoParameterCLM m w < 1 at hw
    linarith
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (one_le_pow₀ hc)

/-- A sharp-exponential-scale angular lower bound; no dimension-dependent
inverse-function neighborhood is left unspecified. -/
theorem markedRealStereoAngularWeight_lintegral_lower (m : ℕ) :
    ENNReal.ofReal ((Real.sqrt Real.pi)^m/Real.Gamma ((m : ℝ)/2+1)) ≤
      ∫⁻ w, markedRealStereoAngularWeight m w := by
  rw [← volume_markedRealStereoSource m]
  calc
    _ = ∫⁻ w, (markedRealStereoSource m).indicator (fun _ => (1 : ℝ≥0∞)) w := by
      rw [lintegral_indicator (isOpen_markedRealStereoSource m).measurableSet]
      simp
    _ ≤ _ := by
      apply lintegral_mono
      intro w
      by_cases hw : w ∈ markedRealStereoSource m
      · rw [Set.indicator_of_mem hw]
        exact markedRealStereoAngularWeight_ge_one m w hw
      · rw [Set.indicator_of_notMem hw]
        exact bot_le

#print axioms markedRealStereoSource_eq_sum_squares
#print axioms isOpen_markedRealStereoSource
#print axioms volume_markedRealStereoSource
#print axioms markedRealStereoAngularWeight_measurable
#print axioms markedRealStereoAngularWeight_ge_one
#print axioms markedRealStereoAngularWeight_lintegral_lower
end SpectralRadiusUpperTail
