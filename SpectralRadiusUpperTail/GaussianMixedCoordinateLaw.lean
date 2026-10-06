import SpectralRadiusUpperTail.GaussianArrayExplicitDensity
import SpectralRadiusUpperTail.RealSchurMixedCoordinateProductVolume
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal

/-- The iid Gaussian law transported to mixed Schur entry coordinates
has the expected normalized Frobenius density. This is an integral
identity, valid for an arbitrary nonnegative test function. -/
theorem gaussianMixedCoordinate_lintegral_density
    {r : ℕ} (s : Fin r → ℕ)
    (g : RealSchurMixedTangent s → ℝ≥0∞) :
    (∫⁻ y, g y ∂(Measure.pi
      (fun _ : RealSchurMixedCoord s × RealSchurMixedCoord s =>
        standardNormal)).map (realSchurMixedFlatEntryEquiv s)) =
      ∫⁻ y,
        ENNReal.ofReal
          (realSchurMixedGaussianCoordinateWeight s y /
            (Real.sqrt (2*Real.pi))^((Fintype.card (RealSchurMixedCoord s))^2)) *
        g y ∂realSchurMixedCoordinateVolume s := by
  let ι := RealSchurMixedCoord s
  let F : ((ι × ι) → ℝ) ≃ᵐ RealSchurMixedTangent s :=
    (realSchurMixedFlatEntryEquiv s).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  let d : ((ι × ι) → ℝ) → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (realGaussianArrayWeight ι x /
      (Real.sqrt (2*Real.pi))^((Fintype.card ι)^2))
  have hd : Measurable d := by
    unfold d realGaussianArrayWeight
    fun_prop
  have hdt (x : (ι × ι) → ℝ) : d x < ∞ := by
    simp [d]
  have hF : (F : ((ι × ι) → ℝ) → RealSchurMixedTangent s) =
      realSchurMixedFlatEntryEquiv s := rfl
  have hvol : Measure.map F (volume : Measure ((ι × ι) → ℝ)) =
      realSchurMixedCoordinateVolume s := by
    rw [hF]
    rfl
  calc
    (∫⁻ y, g y ∂(Measure.pi
      (fun _ : ι × ι => standardNormal)).map
        (realSchurMixedFlatEntryEquiv s)) =
        ∫⁻ x, g (F x) ∂Measure.pi
          (fun _ : ι × ι => standardNormal) := by
      rw [← hF]
      exact lintegral_map_equiv g F
    _ = ∫⁻ x, d x * g (F x) ∂(volume : Measure ((ι × ι) → ℝ)) := by
      rw [gaussianArrayLaw_eq_explicitDensity]
      exact lintegral_withDensity_eq_lintegral_mul_non_measurable
        volume hd (Filter.Eventually.of_forall hdt) (g ∘ F)
    _ = ∫⁻ y, d (F.symm y) * g y
          ∂realSchurMixedCoordinateVolume s := by
      rw [← hvol]
      have hmap := lintegral_map_equiv
        (μ := (volume : Measure ((ι × ι) → ℝ)))
        (fun y => d (F.symm y) * g y) F
      rw [hmap]
      simp
    _ = ∫⁻ y,
        ENNReal.ofReal
          (realSchurMixedGaussianCoordinateWeight s y /
            (Real.sqrt (2*Real.pi))^((Fintype.card ι)^2)) *
        g y ∂realSchurMixedCoordinateVolume s := by
      rfl

#print axioms gaussianMixedCoordinate_lintegral_density
end SpectralRadiusUpperTail
