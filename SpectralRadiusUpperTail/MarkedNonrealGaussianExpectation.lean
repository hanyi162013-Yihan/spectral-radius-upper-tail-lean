import SpectralRadiusUpperTail.MarkedNonrealGaussianArea
import SpectralRadiusUpperTail.GaussianMixedCoordinateLaw

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix Matrix.Norms.Operator

noncomputable def MarkedNonrealFlagAtlas.coefficient
    {m : ℕ} {hm : 0 < m} (F : MarkedNonrealFlagAtlas m hm) : ℝ≥0∞ :=
  (ENNReal.ofReal ((Real.sqrt (2*Real.pi))^
    ((Fintype.card (MarkedNonrealIndex m))^2)))⁻¹ *
      (F.angularMass*markedNonrealUpperMass m)

/-- The global marked-pair formula is now an identity under the actual
independent standard real Gaussian entry law. -/
theorem MarkedNonrealFlagAtlas.gaussian_expectation
    {m : ℕ} {hm : 0 < m} (F : MarkedNonrealFlagAtlas m hm)
    (g : ℂ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ a : MarkedNonrealIndex m × MarkedNonrealIndex m → ℝ,
      markedNonrealRootWeight m (Matrix.of a.curry) g
        ∂Measure.pi (fun _ => standardNormal)) =
      F.coefficient*markedNonrealDiagonalIntegral m g := by
  let s := markedNonrealBlockSizes m
  let G := fun y : RealSchurMixedTangent s =>
    markedNonrealRootWeight m ((realSchurMixedEntryEquiv s).symm y) g
  let E := (realSchurMixedFlatEntryEquiv s).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have hG (a : MarkedNonrealIndex m × MarkedNonrealIndex m → ℝ) :
      G (E a)=markedNonrealRootWeight m (Matrix.of a.curry) g := by
    change markedNonrealRootWeight m ((realSchurMixedEntryEquiv s).symm
      ((realSchurMixedEntryEquiv s) ((realMatrixEntryEquiv (MarkedNonrealIndex m)).symm a))) g=_
    rw [LinearEquiv.symm_apply_apply]
    rfl
  have ht := lintegral_map_equiv
    (μ := Measure.pi (fun _ : MarkedNonrealIndex m × MarkedNonrealIndex m => standardNormal)) G E
  simp_rw [hG] at ht
  have he := gaussianMixedCoordinate_lintegral_density s G
  change (∫⁻ y, G y ∂Measure.map E
    (Measure.pi (fun _ : MarkedNonrealIndex m × MarkedNonrealIndex m => standardNormal)))=_ at he
  rw [← ht,he]
  let C : ℝ := (Real.sqrt (2*Real.pi))^((Fintype.card (MarkedNonrealIndex m))^2)
  have hC : 0 < C := by dsimp [C]; positivity
  have hpoint (y : RealSchurMixedTangent s) :
      ENNReal.ofReal (realSchurMixedGaussianCoordinateWeight s y/C)*G y=
        (ENNReal.ofReal C)⁻¹*
          (ENNReal.ofReal (realSchurMixedGaussianCoordinateWeight s y)*G y) := by
    rw [ENNReal.ofReal_div_of_pos hC,div_eq_mul_inv]
    ac_rfl
  change (∫⁻ y, ENNReal.ofReal (realSchurMixedGaussianCoordinateWeight s y/C)*G y
    ∂realSchurMixedCoordinateVolume s)=_
  simp_rw [hpoint]
  rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hC).ne')]
  rw [F.gaussian_area g hg]
  unfold MarkedNonrealFlagAtlas.coefficient
  dsimp only [C]
  ac_rfl

theorem markedNonrealRootWeight_expectation_one_le (m : ℕ) :
    (∫⁻ a : MarkedNonrealIndex m × MarkedNonrealIndex m → ℝ,
      markedNonrealRootWeight m (Matrix.of a.curry) (fun _ => 1)
        ∂Measure.pi (fun _ => standardNormal)) ≤ (m+2 : ℕ) := by
  calc
    _ ≤ ∫⁻ _a : MarkedNonrealIndex m × MarkedNonrealIndex m → ℝ, (m+2 : ℕ)
        ∂Measure.pi (fun _ => standardNormal) :=
      lintegral_mono (fun a => markedNonrealRootWeight_one_le m (Matrix.of a.curry))
    _ = _ := by simp

#print axioms MarkedNonrealFlagAtlas.gaussian_expectation
#print axioms markedNonrealRootWeight_expectation_one_le
end SpectralRadiusUpperTail
