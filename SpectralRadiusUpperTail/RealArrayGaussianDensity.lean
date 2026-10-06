import SpectralRadiusUpperTail.PiRealDensity
import SpectralRadiusUpperTail.RealGaussianMatrixExplicitDensity

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal BigOperators

/-- An unnormalized Gaussian on an arbitrary finite real array. -/
noncomputable def realArrayGaussianMeasure {ι : Type*} [Fintype ι] (n : ℝ) : Measure (ι → ℝ) :=
  volume.withDensity (fun a => ENNReal.ofReal (Real.exp (-(n/2)*∑ i, (a i)^2)))

theorem realArrayGaussianWeight_prod {ι : Type*} [Fintype ι] (n : ℝ) (a : ι → ℝ) :
    Real.exp (-(n/2)*∑ i, (a i)^2)=∏ i, Real.exp (-(n/2)*(a i)^2) := by
  rw [← Real.exp_sum,← Finset.mul_sum]

theorem realArrayGaussianWeight_integrable {ι : Type*} [Fintype ι]
    (n : ℝ) (hn : 0 < n) :
    Integrable (fun a : ι → ℝ => Real.exp (-(n/2)*∑ i, (a i)^2)) := by
  simp_rw [realArrayGaussianWeight_prod]
  exact Integrable.fintype_prod (fun _ => integrable_exp_neg_mul_sq (by linarith : 0 < n/2))

theorem realArrayGaussianMeasure_finite {ι : Type*} [Fintype ι] (n : ℝ) (hn : 0 < n) :
    IsFiniteMeasure (realArrayGaussianMeasure (ι := ι) n) := by
  apply isFiniteMeasure_withDensity
  rw [← ofReal_integral_eq_lintegral_ofReal (realArrayGaussianWeight_integrable n hn)
    (Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le))]
  exact ENNReal.ofReal_ne_top

/-- The density-product identity also applies to blocks of different dimensions. -/
theorem dependent_pi_withDensity_ofReal {ι : Type*} [Fintype ι]
    {E : ι → Type*} [∀ i, MeasurableSpace (E i)]
    (μ : (i : ι) → Measure (E i)) [∀ i, SigmaFinite (μ i)]
    (f : (i : ι) → E i → ℝ) (hf : ∀ i, Integrable (f i) (μ i)) (hn : ∀ i x, 0 ≤ f i x) :
    (Measure.pi μ).withDensity (fun x => ENNReal.ofReal (∏ i, f i (x i))) =
      Measure.pi (fun i => (μ i).withDensity (fun x => ENNReal.ofReal (f i x))) := by
  have (i : ι) : IsFiniteMeasure ((μ i).withDensity (fun x => ENNReal.ofReal (f i x))) := by
    apply isFiniteMeasure_withDensity
    rw [← ofReal_integral_eq_lintegral_ofReal (hf i) (Filter.Eventually.of_forall (hn i))]
    exact ENNReal.ofReal_ne_top
  symm
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),Measure.restrict_pi_pi]
  have hi := Integrable.fintype_prod_dep (fun i => (hf i).restrict (s := s i))
  have hnn : ∀ x : (i : ι) → E i, 0 ≤ ∏ i, f i (x i) :=
    fun x => Finset.prod_nonneg (fun i _ => hn i (x i))
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hnn),
    integral_fintype_prod_eq_prod]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (hn i))]
  apply Finset.prod_congr rfl
  intro i hi
  rw [withDensity_apply _ (hs i)]
  exact ofReal_integral_eq_lintegral_ofReal ((hf i).restrict (s := s i))
    (Filter.Eventually.of_forall (hn i))

#print axioms realArrayGaussianWeight_integrable
#print axioms realArrayGaussianMeasure_finite
#print axioms dependent_pi_withDensity_ofReal
end SpectralRadiusUpperTail
