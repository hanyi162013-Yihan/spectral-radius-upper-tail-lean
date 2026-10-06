import SpectralRadiusUpperTail.MarkedNonrealCodeGaussianIntegral
import SpectralRadiusUpperTail.MarkedNonrealRootWeight
import SpectralRadiusUpperTail.RealSchurDiagonalCodePartition
import SpectralRadiusUpperTail.RealSchurMixedSimpleSpectrumVolume

namespace SpectralRadiusUpperTail
open MeasureTheory Classical
open scoped ENNReal Matrix Matrix.Norms.Operator

noncomputable def markedNonrealDiagonalIntegral (m : ℕ) (g : ℂ → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ d : RealSchurMixedDiagonalEntry (markedNonrealBlockSizes m) → ℝ,
    ENNReal.ofReal (realSchurMixedDiagonalGaussianJacobian (markedNonrealBlockSizes m) d)*
      markedNonrealDiagonalWeight m g d

/-- Global marked-pair area formula, with no unspecified overlap factor.
The angular mass is kept explicit for subsequent normalization. -/
theorem MarkedNonrealFlagAtlas.gaussian_area
    {m : ℕ} {hm : 0 < m} (F : MarkedNonrealFlagAtlas m hm)
    (g : ℂ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ y, ENNReal.ofReal (realSchurMixedGaussianCoordinateWeight (markedNonrealBlockSizes m) y)*
      markedNonrealRootWeight m ((realSchurMixedEntryEquiv (markedNonrealBlockSizes m)).symm y) g
      ∂realSchurMixedCoordinateVolume (markedNonrealBlockSizes m)) =
      F.angularMass*(markedNonrealDiagonalIntegral m g*markedNonrealUpperMass m) := by
  let s := markedNonrealBlockSizes m
  let A := fun y : RealSchurMixedTangent s => (realSchurMixedEntryEquiv s).symm y
  let w := fun y => ENNReal.ofReal (realSchurMixedGaussianCoordinateWeight s y)
  let S := fun code : MarkedNonrealCode m => A ⁻¹' realSchurMixedCodeClass s code
  let G := fun code : MarkedNonrealCode m =>
    (S code).indicator (fun y => w y*markedNonrealCodeWeight m (A y) code g)
  have hA : Measurable A := (realSchurMixedEntryEquiv s).symm.toContinuousLinearEquiv.continuous.measurable
  have hW : Continuous (realMatrixGaussianWeight (MarkedNonrealIndex m)) := by
    unfold realMatrixGaussianWeight
    fun_prop
  have hw : Measurable w :=
    (hW.comp (realSchurMixedEntryEquiv s).symm.toContinuousLinearEquiv.continuous).measurable.ennreal_ofReal
  have hS (code : MarkedNonrealCode m) : MeasurableSet (S code) :=
    (measurableSet_realSchurMixedCodeClass s (markedNonrealBlockSizes_pos m hm) code).preimage hA
  have hG (code : MarkedNonrealCode m) : Measurable (G code) :=
    (hw.mul ((markedNonrealCodeWeight_measurable m code g hg).comp hA)).indicator (hS code)
  have hpoint : ∀ᵐ y ∂realSchurMixedCoordinateVolume s,
      w y*markedNonrealRootWeight m (A y) g=∑ code : MarkedNonrealCode m, G code y := by
    filter_upwards [realSchurMixed_charpoly_separable_ae_coordinateVolume s] with y hy
    have hs := markedNonreal_realized_code_weight_sum m hm (A y) hy g
    change (∑ code : MarkedNonrealCode m, if A y ∈ realSchurMixedCodeClass s code then
      markedNonrealCodeWeight m (A y) code g else 0)=markedNonrealRootWeight m (A y) g at hs
    rw [← hs,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro code hcode
    by_cases hc : A y ∈ realSchurMixedCodeClass s code
    · simp [G,S,hc]
    · simp [G,S,hc]
  calc
    _ = ∫⁻ y, ∑ code : MarkedNonrealCode m, G code y ∂realSchurMixedCoordinateVolume s :=
      lintegral_congr_ae hpoint
    _ = ∑ code : MarkedNonrealCode m, ∫⁻ y, G code y ∂realSchurMixedCoordinateVolume s :=
      lintegral_finsetSum Finset.univ (fun code _ => hG code)
    _ = ∑ code : MarkedNonrealCode m,
        F.angularMass*(markedNonrealDiagonalCodeIntegral m code g*markedNonrealUpperMass m) := by
      apply Finset.sum_congr rfl
      intro code hcode
      change (∫⁻ y, (S code).indicator
        (fun y => w y*markedNonrealCodeWeight m (A y) code g) y
        ∂realSchurMixedCoordinateVolume s)=_
      rw [lintegral_indicator (hS code)]
      exact F.code_gaussian_integral code g hg
    _ = F.angularMass*((∑ code : MarkedNonrealCode m,
        markedNonrealDiagonalCodeIntegral m code g)*markedNonrealUpperMass m) := by
      rw [← Finset.mul_sum,← Finset.sum_mul]
    _ = _ := by
      congr 2
      exact realSchurMixedDiagonalCodeSource_integral_sum s
        (fun d => ENNReal.ofReal (realSchurMixedDiagonalGaussianJacobian s d)*
          markedNonrealDiagonalWeight m g d)

#print axioms MarkedNonrealFlagAtlas.gaussian_area
end SpectralRadiusUpperTail
