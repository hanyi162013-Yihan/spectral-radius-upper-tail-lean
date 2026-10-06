import SpectralRadiusUpperTail.NormalizedVariation
import SpectralRadiusUpperTail.CenteredCoupling

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- A small unnormalized weighted likelihood error controls the actual centered
coupling error, including normalization, both marginals, and integrability. -/
theorem normalized_likelihood_coupling (μ : Measure E) [IsProbabilityMeasure μ]
    (g : E → ℝ) (hg : Measurable g) (hgint : Integrable g μ) (hgn : ∀ x, 0 ≤ g x)
    (h2 : Integrable (fun x : E => ‖x‖^2) μ)
    (heint : Integrable (fun x => (1+‖x‖^2)*|g x-1|) μ)
    (ε : ℝ) (hε : 0 ≤ ε) (hεhalf : ε ≤ 1/2)
    (herr : (∫ x, (1+‖x‖^2)*|g x-1| ∂μ) ≤ ε) :
    let Z := ∫ x, g x ∂μ
    let k := fun x => g x/Z
    let π := densityCoupling μ (fun x => ENNReal.ofReal (k x))
    1/2 ≤ Z ∧ IsProbabilityMeasure π ∧
      π.map Prod.fst = μ.withDensity (fun x => ENNReal.ofReal (k x)) ∧
      π.map Prod.snd = μ ∧
      Integrable (fun z : E × E => z.1-z.2) π ∧
      (∫ z, ‖(z.1-z.2) - ∫ w, w.1-w.2 ∂π‖^2 ∂π) ≤
        4*ε*(2+∫ x : E, ‖x‖^2 ∂μ) := by
  let Z := ∫ x, g x ∂μ
  let k := fun x => g x/Z
  let f := fun x : E => 1+‖x‖^2
  have hf : Integrable f μ := (integrable_const 1).add h2
  obtain ⟨hZhalf, hvi, hv⟩ := weighted_normalized_variation_small μ g f hgint hf
    (fun x => le_add_of_nonneg_right (sq_nonneg _)) heint ε (∫ x, f x ∂μ)
    hε hεhalf herr le_rfl
  have hZ : 0 < Z := lt_of_lt_of_le (by norm_num) hZhalf
  have hk : Measurable k := hg.div_const Z
  have hkn (x : E) : 0 ≤ k x := div_nonneg (hgn x) hZ.le
  have hki : Integrable k μ := hgint.div_const Z
  have hki1 : (∫ x, k x ∂μ) = 1 := by
    rw [show k = (fun x => g x/Z) from rfl, integral_div]
    exact div_self (ne_of_gt hZ)
  have hnorm : (∫⁻ x, ENNReal.ofReal (k x) ∂μ) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hki (Filter.Eventually.of_forall hkn), hki1]
    exact ENNReal.ofReal_one
  have hkm : Measurable (fun x : E => |k x-1|) := by
    simpa only [Real.norm_eq_abs] using
      (show Measurable (fun x : E => k x-1) from hk.sub measurable_const).norm
  have hm : Measurable (fun x : E => |k x-1| *‖x‖^2) :=
    hkm.mul (continuous_norm.pow 2).measurable
  have hp (x : E) : |k x-1| *‖x‖^2 ≤ f x * |k x-1| := by
    dsimp [f]
    nlinarith [abs_nonneg (k x-1)]
  have hw : Integrable (fun x : E => |k x-1| *‖x‖^2) μ :=
    hvi.mono_nonneg hm.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => mul_nonneg (abs_nonneg _) (sq_nonneg _)))
      (Filter.Eventually.of_forall hp)
  have hwb := (integral_mono hw hvi hp).trans hv
  have hfm : (∫ x, f x ∂μ) = 1 + ∫ x : E, ‖x‖^2 ∂μ := by
    change (∫ x : E, 1+‖x‖^2 ∂μ) = _
    rw [integral_add (integrable_const 1) h2]
    simp only [integral_const, probReal_univ, one_smul]
  have hmarg := densityCoupling_marginals μ _ hk.ennreal_ofReal hnorm
  have hmom := densityCoupling_difference_moments μ k hk hkn hnorm hw
  refine ⟨hZhalf, densityCoupling_probability μ _ hk.ennreal_ofReal hnorm,
    hmarg.1, hmarg.2, hmom.1, ?_⟩
  have hc := densityCoupling_centered_secondMoment_le μ k hk hkn hnorm hw
  apply hc.trans
  rw [hfm] at hwb
  linarith

#print axioms normalized_likelihood_coupling
end SpectralRadiusUpperTail
