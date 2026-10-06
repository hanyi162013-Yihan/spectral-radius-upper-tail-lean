import SpectralRadiusUpperTail.CommonPartCoupling
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal
variable {α : Type*} [MeasurableSpace α]

noncomputable def commonDensityPart (μ : Measure α) (k : α → ℝ≥0∞) : Measure α :=
  μ.withDensity (fun x => min (k x) 1)
noncomputable def positiveDensityResidual (μ : Measure α) (k : α → ℝ≥0∞) : Measure α :=
  μ.withDensity (fun x => k x - min (k x) 1)
noncomputable def negativeDensityResidual (μ : Measure α) (k : α → ℝ≥0∞) : Measure α :=
  μ.withDensity (fun x => 1 - min (k x) 1)
noncomputable def densityCoupling (μ : Measure α) (k : α → ℝ≥0∞) : Measure (α × α) :=
  commonPartCoupling (commonDensityPart μ k)
    (positiveDensityResidual μ k) (negativeDensityResidual μ k)

lemma commonDensityPart_le_base (μ : Measure α) (k : α → ℝ≥0∞) :
    commonDensityPart μ k ≤ μ := by
  calc
    _ ≤ μ.withDensity (fun _ => 1) :=
      withDensity_mono (Filter.Eventually.of_forall (fun x => min_le_right (k x) 1))
    _ = μ := by simp [withDensity_const]

lemma positiveDensityResidual_le_tilt (μ : Measure α) (k : α → ℝ≥0∞) :
    positiveDensityResidual μ k ≤ μ.withDensity k :=
  withDensity_mono (Filter.Eventually.of_forall (fun x => tsub_le_self))

lemma negativeDensityResidual_le_base (μ : Measure α) (k : α → ℝ≥0∞) :
    negativeDensityResidual μ k ≤ μ := by
  calc
    _ ≤ μ.withDensity (fun _ => 1) :=
      withDensity_mono (Filter.Eventually.of_forall (fun _ => tsub_le_self))
    _ = μ := by simp [withDensity_const]

lemma commonDensity_add_positive (μ : Measure α) (k : α → ℝ≥0∞) (hk : Measurable k) :
    commonDensityPart μ k + positiveDensityResidual μ k = μ.withDensity k := by
  unfold commonDensityPart positiveDensityResidual
  rw [← withDensity_add_left (hk.min measurable_const)]
  congr 1
  funext x
  exact add_tsub_cancel_of_le (min_le_left (k x) 1)

lemma commonDensity_add_negative (μ : Measure α) (k : α → ℝ≥0∞) (hk : Measurable k) :
    commonDensityPart μ k + negativeDensityResidual μ k = μ := by
  unfold commonDensityPart negativeDensityResidual
  rw [← withDensity_add_left (hk.min measurable_const)]
  have hfun : (fun x => min (k x) 1) + (fun x => 1-min (k x) 1) = fun _ => 1 := by
    funext x
    exact add_tsub_cancel_of_le (min_le_right (k x) 1)
  rw [hfun]
  simp [withDensity_const]

lemma normalizedDensity_probability (μ : Measure α) (k : α → ℝ≥0∞)
    (hnorm : (∫⁻ x, k x ∂μ) = 1) : IsProbabilityMeasure (μ.withDensity k) := by
  constructor
  simpa only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] using hnorm

instance commonDensityPart_isFiniteMeasure (μ : Measure α) [IsFiniteMeasure μ]
    (k : α → ℝ≥0∞) : IsFiniteMeasure (commonDensityPart μ k) :=
  isFiniteMeasure_of_le μ (commonDensityPart_le_base μ k)

instance negativeDensityResidual_isFiniteMeasure (μ : Measure α) [IsFiniteMeasure μ]
    (k : α → ℝ≥0∞) : IsFiniteMeasure (negativeDensityResidual μ k) :=
  isFiniteMeasure_of_le μ (negativeDensityResidual_le_base μ k)

lemma density_residual_masses_eq (μ : Measure α) [IsProbabilityMeasure μ]
    (k : α → ℝ≥0∞) (hk : Measurable k) (hnorm : (∫⁻ x, k x ∂μ) = 1) :
    negativeDensityResidual μ k Set.univ = positiveDensityResidual μ k Set.univ := by
  have : IsProbabilityMeasure (μ.withDensity k) := normalizedDensity_probability μ k hnorm
  apply (ENNReal.add_right_inj (measure_ne_top (commonDensityPart μ k) Set.univ)).mp
  have hp := congrArg (fun ν : Measure α => ν Set.univ) (commonDensity_add_positive μ k hk)
  have hq := congrArg (fun ν : Measure α => ν Set.univ) (commonDensity_add_negative μ k hk)
  simp only [Measure.add_apply, measure_univ] at hp hq
  exact hq.trans hp.symm

/-- An actual coupling of the normalized tilted law and the original law. -/
theorem densityCoupling_marginals (μ : Measure α) [IsProbabilityMeasure μ]
    (k : α → ℝ≥0∞) (hk : Measurable k) (hnorm : (∫⁻ x, k x ∂μ) = 1) :
    (densityCoupling μ k).map Prod.fst = μ.withDensity k ∧
      (densityCoupling μ k).map Prod.snd = μ := by
  have : IsProbabilityMeasure (μ.withDensity k) := normalizedDensity_probability μ k hnorm
  have : IsFiniteMeasure (positiveDensityResidual μ k) :=
    isFiniteMeasure_of_le (μ.withDensity k) (positiveDensityResidual_le_tilt μ k)
  have hm := density_residual_masses_eq μ k hk hnorm
  constructor
  · exact (commonPartCoupling_map_fst _ _ _ hm).trans (commonDensity_add_positive μ k hk)
  · exact (commonPartCoupling_map_snd _ _ _ hm).trans (commonDensity_add_negative μ k hk)

theorem densityCoupling_probability (μ : Measure α) [IsProbabilityMeasure μ]
    (k : α → ℝ≥0∞) (hk : Measurable k) (hnorm : (∫⁻ x, k x ∂μ) = 1) :
    IsProbabilityMeasure (densityCoupling μ k) := by
  constructor
  have h := congrArg (fun ν : Measure α => ν Set.univ) (densityCoupling_marginals μ k hk hnorm).2
  simpa only [Measure.map_apply measurable_snd MeasurableSet.univ,
    Set.preimage_univ, measure_univ] using h

#print axioms densityCoupling_marginals
#print axioms densityCoupling_probability
end SpectralRadiusUpperTail
