import SpectralRadiusUpperTail.Centering
import SpectralRadiusUpperTail.DensityCost
import SpectralRadiusUpperTail.TwoCoordinateSquareExp
import SpectralRadiusUpperTail.SoftNormalizer

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A positive square-exponential moment supplies actual first and second moments. -/
theorem squareExp_moments (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E)
    (hX : AEStronglyMeasurable X μ) (c : ℝ) (hc : 0 < c)
    (he : Integrable (fun x => Real.exp (c*‖X x‖^2)) μ) :
    Integrable X μ ∧ Integrable (fun x => ‖X x‖^2) μ := by
  have hb (x : Ω) : ‖X x‖^2 ≤ Real.exp (c*‖X x‖^2)/c := by
    apply (le_div_iff₀ hc).mpr
    have hh := Real.add_one_le_exp (c*‖X x‖^2)
    nlinarith
  have h2 : Integrable (fun x => ‖X x‖^2) μ :=
    (he.div_const c).mono_nonneg (hX.norm.pow 2)
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
      (Filter.Eventually.of_forall hb)
  exact ⟨((memLp_two_iff_integrable_sq_norm hX).mpr h2).integrable
    (by norm_num : (1 : ℝ≥0∞) ≤ 2), h2⟩

/-- Centering loses a factor two in the exponent and squares the moment bound.
The centering vector is the actual Bochner expectation. -/
theorem centered_squareExp (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E)
    (hX : AEStronglyMeasurable X μ) (c M : ℝ) (hc : 0 < c)
    (he : Integrable (fun x => Real.exp (c*‖X x‖^2)) μ)
    (hM : (∫ x, Real.exp (c*‖X x‖^2) ∂μ) ≤ M) :
    Integrable (fun x => Real.exp ((c/2)*‖X x-∫ y, X y ∂μ‖^2)) μ ∧
      (∫ x, Real.exp ((c/2)*‖X x-∫ y, X y ∂μ‖^2) ∂μ) ≤ M^2 := by
  let m := ∫ y, X y ∂μ
  obtain ⟨h1, h2⟩ := squareExp_moments μ X hX c hc he
  have hm2 : ‖m‖^2 ≤ ∫ x, ‖X x‖^2 ∂μ := by
    have hh := integral_centered_norm_sq μ X h1 h2
    have hn : 0 ≤ ∫ x, ‖X x-m‖^2 ∂μ := integral_nonneg (fun _ => sq_nonneg _)
    dsimp [m] at hn ⊢
    linarith
  have hj := convexOn_exp.map_integral_le (μ := μ) Real.continuous_exp.continuousOn
    isClosed_univ (Filter.Eventually.of_forall (fun _ => Set.mem_univ _))
    (h2.const_mul c) he
  have hm : Real.exp (c*‖m‖^2) ≤ M := by
    apply (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hm2 hc.le)).trans
    have hj' : Real.exp (c*(∫ x, ‖X x‖^2 ∂μ)) ≤
        ∫ x, Real.exp (c*‖X x‖^2) ∂μ := by
      simpa only [integral_const_mul] using hj
    exact hj'.trans hM
  have hMn : 0 ≤ M := (Real.exp_pos _).le.trans hm
  have hb (x : Ω) : Real.exp ((c/2)*‖X x-m‖^2) ≤ M*Real.exp (c*‖X x‖^2) := by
    calc
      _ ≤ Real.exp (c*‖X x‖^2+c*‖m‖^2) := Real.exp_le_exp.mpr (by
        have hh := mul_le_mul_of_nonneg_left (norm_sub_sq_le_twice (X x) m) (by positivity : 0 ≤ c/2)
        nlinarith)
      _ = Real.exp (c*‖X x‖^2)*Real.exp (c*‖m‖^2) := Real.exp_add _ _
      _ ≤ Real.exp (c*‖X x‖^2)*M := mul_le_mul_of_nonneg_left hm (Real.exp_nonneg _)
      _ = _ := mul_comm _ _
  have hi : Integrable (fun x => Real.exp ((c/2)*‖X x-m‖^2)) μ :=
    (he.const_mul M).mono_nonneg
      (Real.continuous_exp.comp_aestronglyMeasurable (((hX.sub aestronglyMeasurable_const).norm.pow 2).const_mul (c/2)))
      (Filter.Eventually.of_forall (fun _ => Real.exp_nonneg _))
      (Filter.Eventually.of_forall hb)
  refine ⟨hi, ?_⟩
  have hh := integral_mono hi (he.const_mul M) hb
  rw [integral_const_mul] at hh
  exact hh.trans (by simpa only [pow_two] using mul_le_mul_of_nonneg_left hM hMn)

#print axioms squareExp_moments
#print axioms centered_squareExp
end SpectralRadiusUpperTail
