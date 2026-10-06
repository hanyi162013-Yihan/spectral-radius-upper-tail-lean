import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.ProbabilityMassFunction.Basic

/-! Finite change-of-measure estimates used in the soft-tilt lower bound.
These are measure-theoretic lemmas, not assumptions of a spectral tail. -/
namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal
variable {Ω : Type*} [MeasurableSpace Ω]

theorem density_event_le (μ : Measure Ω) (f : Ω → ℝ≥0∞)
    (A : Set Ω) (hA : MeasurableSet A) (C : ℝ≥0∞)
    (hbound : ∀ x ∈ A, f x ≤ C) :
    μ.withDensity f A ≤ C * μ A := by
  rw [withDensity_apply f hA]
  calc
    ∫⁻ x in A, f x ∂μ ≤ ∫⁻ _x in A, C ∂μ := by
      exact setLIntegral_mono' hA hbound
    _ = C * μ A := by simp

/-- A likelihood bound on the good event gives a lower bound under the original law. -/
theorem change_measure_good_event (μ : Measure Ω) (f : Ω → ℝ≥0∞)
    (A B : Set Ω) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (C : ℝ≥0∞) (hC₀ : C ≠ 0) (hCtop : C ≠ ∞)
    (hbound : ∀ x ∈ B, f x ≤ C) :
    μ.withDensity f (A ∩ B) / C ≤ μ A := by
  apply (ENNReal.div_le_iff' hC₀ hCtop).2
  calc
    μ.withDensity f (A ∩ B) ≤ C * μ (A ∩ B) :=
      density_event_le μ f (A ∩ B) (hA.inter hB) C (fun x hx => hbound x hx.2)
    _ ≤ C * μ A := mul_le_mul' le_rfl (measure_mono Set.inter_subset_left)

noncomputable def normalizedTilt (μ : Measure Ω) (w : Ω → ℝ≥0∞) : Measure Ω :=
  μ.withDensity (fun x => w x / ∫⁻ y, w y ∂μ)

theorem normalizedTilt_probability (μ : Measure Ω) (w : Ω → ℝ≥0∞)
    (hZ₀ : (∫⁻ y, w y ∂μ) ≠ 0) (hZtop : (∫⁻ y, w y ∂μ) ≠ ∞) :
    IsProbabilityMeasure (normalizedTilt μ w) := by
  constructor
  rw [normalizedTilt, withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  simp only [div_eq_mul_inv]
  rw [lintegral_mul_const', ENNReal.mul_inv_cancel hZ₀ hZtop]
  exact ENNReal.inv_ne_top.mpr hZ₀

/-- In particular, an exponentially small normalizer cannot spoil an n²-scale exception. -/
theorem normalizedTilt_exception_le (μ : Measure Ω) (w : Ω → ℝ≥0∞)
    (A : Set Ω) (hA : MeasurableSet A) (hw : ∀ x, w x ≤ 1) :
    normalizedTilt μ w A ≤ (∫⁻ y, w y ∂μ)⁻¹ * μ A := by
  apply density_event_le μ _ A hA _
  intro x _
  simpa only [div_eq_mul_inv, one_mul] using
    mul_le_mul' (hw x) (le_refl (∫⁻ y, w y ∂μ)⁻¹)

#print axioms density_event_le
#print axioms change_measure_good_event
#print axioms normalizedTilt_probability
#print axioms normalizedTilt_exception_le
end SpectralRadiusUpperTail
