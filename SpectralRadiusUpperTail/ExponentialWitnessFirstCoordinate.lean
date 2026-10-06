import SpectralRadiusUpperTail.NormalizedExponentialWitnessBound
import SpectralRadiusUpperTail.ExponentialTail

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

noncomputable def exponentialWitnessIntegrand {m : ℕ} (N u h₀ : ℝ) (h : Fin m → ℝ)
    (y₀ : ℝ) (y : Fin m → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(N/u)*((h₀*y₀+∑ i, h i*y i)/(y₀+∑ i, y i))))

lemma exponentialWitnessIntegrand_measurable (m : ℕ) (N u h₀ : ℝ) (h : Fin m → ℝ) :
    Measurable (fun y : ℝ × (Fin m → ℝ) => exponentialWitnessIntegrand N u h₀ h y.1 y.2) := by
  unfold exponentialWitnessIntegrand
  fun_prop

lemma exponential_witness_first_coordinate {m : ℕ} (N u h₀ : ℝ) (h y : Fin m → ℝ)
    (hN : 0 < N) (hu : 0 < u) (hy : ∀ i, 0 ≤ y i) (hmin : ∀ i, h₀ ≤ h i)
    (hsum : ∑ i, y i ≤ 2*N) :
    ENNReal.ofReal (Real.exp (-N*h₀/u)*Real.exp (-(∑ i, (h i-h₀)*y i)/(2*u))) *
      ENNReal.ofReal (Real.exp (-(1/2 : ℝ)*(2*N-∑ i, y i))) ≤
    ∫⁻ y₀ : ℝ, exponentialWitnessIntegrand N u h₀ h y₀ y ∂expMeasure (1/2) := by
  let t := 2*N-∑ i, y i
  have ht : 0 ≤ t := sub_nonneg.mpr hsum
  let C := ENNReal.ofReal (Real.exp (-N*h₀/u)*Real.exp (-(∑ i, (h i-h₀)*y i)/(2*u)))
  have hmono : (∫⁻ _y₀ in Ioi t, C ∂expMeasure (1/2)) ≤
      ∫⁻ y₀ in Ioi t, exponentialWitnessIntegrand N u h₀ h y₀ y ∂expMeasure (1/2) := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y₀ hy₀
    apply ENNReal.ofReal_le_ofReal
    apply normalized_exponential_weight_lower N u h₀ y₀ h y hN hu hy hmin
    change t < y₀ at hy₀
    dsimp [t] at hy₀
    linarith
  have he : (∫⁻ _y₀ in Ioi t, C ∂expMeasure (1/2)) =
      C * ENNReal.ofReal (Real.exp (-(1/2 : ℝ)*t)) := by
    rw [lintegral_const, Measure.restrict_apply_univ,
      exponential_tail (1/2) t (by norm_num) ht]
    simp only [neg_mul]
  rw [he] at hmono
  exact hmono.trans (setLIntegral_le_lintegral _ _)

#print axioms exponentialWitnessIntegrand
#print axioms exponentialWitnessIntegrand_measurable
#print axioms exponential_witness_first_coordinate
end SpectralRadiusUpperTail
