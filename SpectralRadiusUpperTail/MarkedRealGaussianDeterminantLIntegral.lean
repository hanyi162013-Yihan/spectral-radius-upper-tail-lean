import SpectralRadiusUpperTail.MarkedRealKernelCharpoly
import SpectralRadiusUpperTail.GaussianMarkedRealDensityMeasurable
import SpectralRadiusUpperTail.GaussianArrayExplicitDensity
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix BigOperators

/-- The complementary-block part of the local Schur integral is exactly
the actual iid-Gaussian absolute characteristic-polynomial moment,
multiplied by its Gaussian partition function. -/
theorem markedReal_gaussianDeterminant_lintegral
    (m : ℕ) (x : ℝ) :
    (∫⁻ a : (Fin m × Fin m) → ℝ,
      ENNReal.ofReal (realGaussianArrayWeight (Fin m) a) *
        ENNReal.ofReal |(Matrix.of a.curry).charpoly.eval x|) =
      ENNReal.ofReal ((Real.sqrt (2*Real.pi))^(m^2)) *
        (∫⁻ a : (Fin m × Fin m) → ℝ,
          ENNReal.ofReal |(Matrix.of a.curry).charpoly.eval x|
            ∂Measure.pi (fun _ => standardNormal)) := by
  let C : ℝ := (Real.sqrt (2*Real.pi))^(m^2)
  let W : ((Fin m × Fin m) → ℝ) → ℝ :=
    realGaussianArrayWeight (Fin m)
  let f : ((Fin m × Fin m) → ℝ) → ℝ≥0∞ :=
    fun a => ENNReal.ofReal |(Matrix.of a.curry).charpoly.eval x|
  let d : ((Fin m × Fin m) → ℝ) → ℝ≥0∞ :=
    fun a => ENNReal.ofReal (W a / C)
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hC0 : ENNReal.ofReal C ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr hC)
  have hCtop : ENNReal.ofReal C ≠ ∞ := ENNReal.ofReal_ne_top
  have hd : Measurable d := by
    dsimp [d, W, realGaussianArrayWeight]
    fun_prop
  have hdtop : ∀ᵐ a ∂(volume : Measure ((Fin m × Fin m) → ℝ)),
      d a < ∞ := Filter.Eventually.of_forall (fun a => by
        simp [d])
  have hnorm :
      (∫⁻ a : (Fin m × Fin m) → ℝ, f a
          ∂Measure.pi (fun _ => standardNormal)) =
        ∫⁻ a : (Fin m × Fin m) → ℝ, d a * f a := by
    rw [gaussianArrayLaw_eq_explicitDensity (Fin m)]
    simpa only [d, W, C, Fintype.card_fin, Pi.mul_apply] using
      (lintegral_withDensity_eq_lintegral_mul_non_measurable
        (volume : Measure ((Fin m × Fin m) → ℝ))
        hd hdtop f)
  have hpoint (a : (Fin m × Fin m) → ℝ) :
      ENNReal.ofReal C * (d a * f a) =
        ENNReal.ofReal (W a) * f a := by
    dsimp [d]
    rw [ENNReal.ofReal_div_of_pos hC]
    rw [← mul_assoc, ENNReal.mul_div_cancel hC0 hCtop]
  change (∫⁻ a, ENNReal.ofReal (W a) * f a) =
    ENNReal.ofReal C * (∫⁻ a, f a
      ∂Measure.pi (fun _ => standardNormal))
  rw [hnorm, ← lintegral_const_mul']
  · exact lintegral_congr_ae
      (Filter.Eventually.of_forall (fun a => (hpoint a).symm))
  · simp

#print axioms markedReal_gaussianDeterminant_lintegral
end SpectralRadiusUpperTail
