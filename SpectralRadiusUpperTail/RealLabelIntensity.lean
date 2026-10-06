import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Classical
open scoped ENNReal BigOperators

/-- The expected counting measure of the real labels of a finite
measurable complex-valued family, retaining multiplicity. -/
noncomputable def realLabelIntensity {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (n : ℕ) (labels : Ω → Fin n → ℂ) : Measure ℝ :=
  ∑ i : Fin n, (μ.restrict {a | (labels a i).im = 0}).map (fun a => (labels a i).re)

instance realLabelIntensity_isFiniteMeasure {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (n : ℕ) (labels : Ω → Fin n → ℂ) :
    IsFiniteMeasure (realLabelIntensity μ n labels) := by
  unfold realLabelIntensity
  infer_instance

theorem realLabelIntensity_lintegral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (n : ℕ) (labels : Ω → Fin n → ℂ)
    (hl : ∀ i, Measurable (fun a => labels a i))
    (w : ℝ → ℝ≥0∞) (hw : Measurable w) :
    (∫⁻ x, w x ∂realLabelIntensity μ n labels) =
      ∫⁻ a, ∑ i : Fin n, if (labels a i).im = 0 then w (labels a i).re else 0 ∂μ := by
  have him (i : Fin n) : MeasurableSet {a | (labels a i).im = 0} :=
    measurableSet_eq_fun (Complex.continuous_im.measurable.comp (hl i)) measurable_const
  have hre (i : Fin n) : Measurable (fun a => (labels a i).re) :=
    Complex.continuous_re.measurable.comp (hl i)
  have hi (i : Fin n) :
      (∫⁻ x, w x ∂(μ.restrict {a | (labels a i).im = 0}).map (fun a => (labels a i).re)) =
      ∫⁻ a, if (labels a i).im = 0 then w (labels a i).re else 0 ∂μ := by
    rw [lintegral_map hw (hre i), ← lintegral_indicator (him i)]
    rfl
  unfold realLabelIntensity
  rw [lintegral_finsetSum_measure]
  simp_rw [hi]
  symm
  exact lintegral_finsetSum _ (fun i _ =>
    Measurable.ite (him i) (hw.comp (hre i)) measurable_const)

theorem realLabelIntensity_open_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (n : ℕ) (labels : Ω → Fin n → ℂ)
    (hl : ∀ i, Measurable (fun a => labels a i)) (b : ℝ) :
    realLabelIntensity μ n labels (Set.Ioi b) =
      ∫⁻ a, ∑ i : Fin n,
        if (labels a i).im = 0 ∧ b < (labels a i).re then (1 : ℝ≥0∞) else 0 ∂μ := by
  have hh := realLabelIntensity_lintegral μ n labels hl
    ((Set.Ioi b).indicator (fun _ => (1 : ℝ≥0∞)))
    (measurable_const.indicator measurableSet_Ioi)
  rw [lintegral_indicator measurableSet_Ioi, setLIntegral_one] at hh
  refine hh.trans (lintegral_congr (fun a => ?_))
  apply Finset.sum_congr rfl
  intro i hi
  by_cases he : (labels a i).im = 0 <;> by_cases hb : b < (labels a i).re <;>
    simp [he,hb]

#print axioms realLabelIntensity_isFiniteMeasure
#print axioms realLabelIntensity_lintegral
#print axioms realLabelIntensity_open_tail
end SpectralRadiusUpperTail
