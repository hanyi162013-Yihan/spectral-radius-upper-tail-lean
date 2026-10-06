import SpectralRadiusUpperTail.ProductRowEnergy
import SpectralRadiusUpperTail.GaussianRowLaw
import SpectralRadiusUpperTail.SoftNormalizer

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators ENNReal

section Shift
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E]

lemma centered_shift_energy (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → E) (hX : MemLp X 2 μ) (hm : (∫ ω, X ω ∂μ) = 0) (t : E) :
    Integrable (fun ω => ‖t-X ω‖^2) μ ∧
      (∫ ω, ‖t-X ω‖^2 ∂μ) = ‖t‖^2 + ∫ ω, ‖X ω‖^2 ∂μ := by
  have hXi := hX.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hX2 := (memLp_two_iff_integrable_sq_norm hX.aestronglyMeasurable).mp hX
  have hh : Integrable (fun ω => 2 * inner ℝ t (X ω)) μ := (hXi.const_inner t).const_mul 2
  have hi := ((integrable_const (‖t‖^2)).sub hh).add hX2
  have hd : Integrable (fun ω => ‖t‖^2-2*inner ℝ t (X ω)) μ :=
    (integrable_const (‖t‖^2)).sub hh
  have hfun : (fun ω => ‖t-X ω‖^2) =
      fun ω => ‖t‖^2-2*inner ℝ t (X ω)+‖X ω‖^2 := by
    funext ω
    exact norm_sub_sq_real t (X ω)
  rw [hfun]
  refine ⟨hi, ?_⟩
  rw [integral_add hd hX2,
    integral_sub (integrable_const _) hh, integral_const_mul, integral_inner hXi, hm]
  simp

end Shift

section Row
variable {𝕂 ι : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂] [Fintype ι]

lemma iid_linear_row_memLp (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (v : ι → 𝕂) (hX : MemLp (fun x : 𝕂 => x) 2 μ) :
    MemLp (fun s : ι → 𝕂 => ∑ i, v i*s i) 2 (Measure.pi (fun _ : ι => μ)) := by
  exact memLp_finsetSum _ (fun i _ =>
    (hX.const_mul (v i)).comp_measurePreserving (measurePreserving_eval _ i))

lemma iid_linear_row_mean (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (v : ι → 𝕂) (hX : MemLp (fun x : 𝕂 => x) 2 μ)
    (hm : (∫ x : 𝕂, x ∂μ) = 0) :
    (∫ s, ∑ i, v i*s i ∂Measure.pi (fun _ : ι => μ)) = 0 := by
  have hi (i : ι) : Integrable (fun s : ι → 𝕂 => v i*s i) (Measure.pi (fun _ : ι => μ)) :=
    ((hX.const_mul (v i)).comp_measurePreserving (measurePreserving_eval _ i)).integrable
      (by norm_num)
  rw [integral_finsetSum _ (fun i _ => hi i)]
  apply Finset.sum_eq_zero
  intro i _
  rw [integral_product_coordinate μ i _ (hX.const_mul (v i)).aestronglyMeasurable,
    integral_const_mul, hm, mul_zero]

theorem iid_shifted_row_energy (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (v : ι → 𝕂) (hX : MemLp (fun x : 𝕂 => x) 2 μ)
    (hm : (∫ x : 𝕂, x ∂μ) = 0) (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1) (t : 𝕂) :
    Integrable (fun s => ‖t-∑ i, v i*s i‖^2) (Measure.pi (fun _ : ι => μ)) ∧
      (∫ s, ‖t-∑ i, v i*s i‖^2 ∂Measure.pi (fun _ : ι => μ)) =
        ‖t‖^2 + ∑ i, ‖v i‖^2 := by
  obtain ⟨hi, he⟩ := centered_shift_energy _ _ (iid_linear_row_memLp μ v hX)
    (iid_linear_row_mean μ v hX hm) t
  exact ⟨hi, he.trans (congrArg (‖t‖^2 + ·) (iid_linear_row_energy μ v hX hm hvar))⟩

end Row

section Normalizer
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂]

/-- Concrete dimension-free lower bound for the normalizer of an iid soft row. -/
theorem gaussianRowNormalizer_lower (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (v : ℕ → 𝕂) (N : ℕ) (hX : MemLp (fun x : 𝕂 => x) 2 μ)
    (hm : (∫ x : 𝕂, x ∂μ) = 0) (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1)
    (hv : ∑ i : Fin N, ‖v i.val‖^2 = 1) (a : ℝ) (ha : 0 < a) (t : 𝕂) :
    ENNReal.ofReal (Real.exp (-(1+‖t‖^2)/a)) ≤ gaussianRowNormalizer μ v a N t := by
  let q := fun s : Fin N → 𝕂 => ‖t-∑ i : Fin N, v i.val*s i‖^2
  have hq : Measurable q := by
    apply Measurable.pow
    · apply Measurable.norm
      apply Measurable.sub measurable_const
      exact Finset.measurable_sum _ (fun i _ => measurable_const.mul (measurable_pi_apply i))
    · exact measurable_const
  obtain ⟨hqi, hqe⟩ := iid_shifted_row_energy μ (fun i : Fin N => v i.val) hX hm hvar t
  have hM : (∫ s, q s ∂Measure.pi (fun _ : Fin N => μ)) ≤ 1+‖t‖^2 := by
    rw [hqe, hv]
    linarith
  have h := soft_normalizer_lower _ q hq hqi (fun _ => sq_nonneg _) a (1+‖t‖^2) ha hM
  have hi := soft_exponential_integrable (Measure.pi (fun _ : Fin N => μ)) q hq
    (fun _ => sq_nonneg _) a ha
  have he := ENNReal.ofReal_le_ofReal h
  rw [ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun _ => Real.exp_nonneg _))] at he
  exact he

end Normalizer
#print axioms iid_shifted_row_energy
#print axioms gaussianRowNormalizer_lower
end SpectralRadiusUpperTail
