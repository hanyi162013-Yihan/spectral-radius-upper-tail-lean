import SpectralRadiusUpperTail.RowProjectionMGF
import SpectralRadiusUpperTail.TwoCoordinateSquareExp
import SpectralRadiusUpperTail.RowSumLawMoments

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators ENNReal

noncomputable def rowSquareExpExponent (τ M : ℝ) : ℝ :=
  (1/(2*(squareExpMgfConstant τ M+1)))^2/4

variable {𝕂 ι : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂] [Fintype ι]

/-- The original entry square-exponential moment implies a uniform positive
square-exponential moment for every finite iid row sum of coefficient energy
at most one, in either field. No symmetry or coordinate independence is assumed. -/
theorem iid_row_squareExp (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (v : ι → 𝕂) (hXi : Integrable (fun x : 𝕂 => x) μ)
    (hm : (∫ x : 𝕂, x ∂μ) = 0) (hv : ∑ i, ‖v i‖^2 ≤ 1)
    (τ : ℝ) (hτ : 0 < τ)
    (hexp : Integrable (fun x : 𝕂 => Real.exp (τ*‖x‖^2)) μ) :
    let c := rowSquareExpExponent τ (∫ x : 𝕂, Real.exp (τ*‖x‖^2) ∂μ)
    0 < c ∧
      Integrable (fun s : ι → 𝕂 => Real.exp (c*‖∑ i, v i*s i‖^2))
        (Measure.pi (fun _ : ι => μ)) ∧
      (∫ s, Real.exp (c*‖∑ i, v i*s i‖^2) ∂Measure.pi (fun _ : ι => μ)) ≤ 2 := by
  let K := squareExpMgfConstant τ (∫ x : 𝕂, Real.exp (τ*‖x‖^2) ∂μ)
  let c₀ := (1/(2*(K+1)))^2/2
  let U := fun s : ι → 𝕂 => ∑ i, v i*s i
  have hK : 0 ≤ K := (squareExpMgfConstant_pos τ _ hτ
    (integral_nonneg (fun _ => Real.exp_nonneg _))).le
  have hU : Measurable U := Finset.measurable_sum _
    (fun i _ => measurable_const.mul (measurable_pi_apply i))
  have hr := quadratic_mgf_squareExp (Measure.pi (fun _ : ι => μ))
    (fun s => RCLike.re (U s)) (RCLike.continuous_re.measurable.comp hU) K hK
    (iid_row_projection_mgf μ v hXi hm hv τ hτ hexp RCLike.reCLM RCLike.abs_re_le_norm)
  have hi := quadratic_mgf_squareExp (Measure.pi (fun _ : ι => μ))
    (fun s => RCLike.im (U s)) (RCLike.continuous_im.measurable.comp hU) K hK
    (iid_row_projection_mgf μ v hXi hm hv τ hτ hexp RCLike.imCLM RCLike.abs_im_le_norm)
  have hh := two_coordinate_squareExp (Measure.pi (fun _ : ι => μ)) U
    hU.aestronglyMeasurable c₀ hr.2.1 hi.2.1 hr.2.2 hi.2.2
  have hc : c₀/2 = rowSquareExpExponent τ (∫ x : 𝕂, Real.exp (τ*‖x‖^2) ∂μ) := by
    dsimp [c₀, K, rowSquareExpExponent]
    ring
  rw [hc] at hh
  refine ⟨?_, hh⟩
  rw [← hc]
  exact div_pos hr.1 (by norm_num)

/-- The uniform estimate is for the actual pushforward future-sum law. -/
theorem iidRowSumLaw_squareExp (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (v : ℕ → 𝕂) (N : ℕ) (hXi : Integrable (fun x : 𝕂 => x) μ)
    (hm : (∫ x : 𝕂, x ∂μ) = 0) (hv : ∑ i : Fin N, ‖v i.val‖^2 ≤ 1)
    (τ : ℝ) (hτ : 0 < τ)
    (hexp : Integrable (fun x : 𝕂 => Real.exp (τ*‖x‖^2)) μ) :
    let c := rowSquareExpExponent τ (∫ x : 𝕂, Real.exp (τ*‖x‖^2) ∂μ)
    0 < c ∧ Integrable (fun x : 𝕂 => Real.exp (c*‖x‖^2)) (iidRowSumLaw μ v N) ∧
      (∫ x : 𝕂, Real.exp (c*‖x‖^2) ∂iidRowSumLaw μ v N) ≤ 2 := by
  obtain ⟨hc, hi, hb⟩ := iid_row_squareExp μ (fun i : Fin N => v i.val) hXi hm hv τ hτ hexp
  refine ⟨hc, ?_, ?_⟩
  · rw [iidRowSumLaw]
    apply (integrable_map_measure (by fun_prop) (iidRowSum_measurable v N).aemeasurable).mpr
    exact hi
  · rw [iidRowSumLaw, integral_map (iidRowSum_measurable v N).aemeasurable (by fun_prop)]
    exact hb

#print axioms iid_row_squareExp
#print axioms iidRowSumLaw_squareExp
end SpectralRadiusUpperTail
