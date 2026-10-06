import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory WithLp
open scoped ENNReal BigOperators

/-- A real coordinate linear equivalence preserving the sum of squares
is an ordinary Euclidean isometry. -/
noncomputable def realArrayEnergyIsometryEquiv
    {ι : Type*} [Fintype ι] (F : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ))
    (hF : ∀ x, (∑ i, (F x i)^2)=∑ i, (x i)^2) :
    EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι := by
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).toLinearEquiv
  let U := (e.trans F).trans e.symm
  refine { U with norm_map' := ?_ }
  intro x
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
  exact hF (ofLp x)

theorem realArrayEnergyEquiv_measurePreserving
    {ι : Type*} [Fintype ι] (F : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ))
    (hF : ∀ x, (∑ i, (F x i)^2)=∑ i, (x i)^2) :
    MeasurePreserving F := by
  let U := realArrayEnergyIsometryEquiv F hF
  have h := (PiLp.volume_preserving_ofLp ι).comp
    (U.measurePreserving.comp (PiLp.volume_preserving_toLp ι))
  exact h

/-- An energy-preserving coordinate change leaves the entire Gaussian
integral invariant, for any measurable nonnegative observable. -/
theorem realArrayGaussian_lintegral_energyEquiv
    {ι : Type*} [Fintype ι] (F : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ))
    (hF : ∀ x, (∑ i, (F x i)^2)=∑ i, (x i)^2)
    (g : (ι → ℝ) → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ x : ι → ℝ, ENNReal.ofReal (Real.exp (-(∑ i, (x i)^2)/2)) * g (F x)) =
      ∫⁻ x : ι → ℝ, ENNReal.ofReal (Real.exp (-(∑ i, (x i)^2)/2)) * g x := by
  have hm : Measurable (fun x : ι → ℝ =>
      ENNReal.ofReal (Real.exp (-(∑ i, (x i)^2)/2)) * g x) := by
    exact (by fun_prop : Measurable (fun x : ι → ℝ =>
      ENNReal.ofReal (Real.exp (-(∑ i, (x i)^2)/2)))).mul hg
  have h := (realArrayEnergyEquiv_measurePreserving F hF).lintegral_comp hm
  simpa only [hF] using h

#print axioms realArrayEnergyIsometryEquiv
#print axioms realArrayEnergyEquiv_measurePreserving
#print axioms realArrayGaussian_lintegral_energyEquiv
end SpectralRadiusUpperTail
