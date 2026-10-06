import SpectralRadiusUpperTail.MarkedNonrealAtlasWeight
import SpectralRadiusUpperTail.RealSchurMixedFlagWeightedGaussian
import SpectralRadiusUpperTail.RealSchurMixedGaussianUpperLIntegral

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix Matrix.Norms.Operator

noncomputable def markedNonrealUpperMass (m : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((Real.sqrt (2*Real.pi))^
    Fintype.card (RealSchurMixedStrictUpperEntry (markedNonrealBlockSizes m)))

noncomputable def markedNonrealDiagonalCodeIntegral (m : ℕ) (code : MarkedNonrealCode m)
    (g : ℂ → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ d in realSchurMixedDiagonalCodeSource (markedNonrealBlockSizes m) code,
    ENNReal.ofReal (realSchurMixedDiagonalGaussianJacobian (markedNonrealBlockSizes m) d)*
      markedNonrealDiagonalWeight m g d

theorem MarkedNonrealFlagAtlas.gaussian_fiber
    {m : ℕ} {hm : 0 < m} (F : MarkedNonrealFlagAtlas m hm)
    (k : ℕ) (code : MarkedNonrealCode m) (g : ℂ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ t in F.source k code,
      ENNReal.ofReal (realSchurMixedJacobianWeight (markedNonrealBlockSizes m) 0 t)*
        (ENNReal.ofReal (realMatrixGaussianWeight (MarkedNonrealIndex m) t.2.val)*
          markedNonrealBlockWeight (markedNonrealFirstBlock m t.2.val) g)
      ∂realSchurMixedCoordinateVolume (markedNonrealBlockSizes m)) =
      F.angleMass k*(markedNonrealDiagonalCodeIntegral m code g*markedNonrealUpperMass m) := by
  have h := realSchurMixedFlagCodedSource_weighted_gaussian (markedNonrealBlockSizes m)
    (markedNonrealBlockSizes_pos m hm) F.marker F.marker_injective F.frames k code
    (markedNonrealDiagonalWeight m g) (fun _ => 1)
    (markedNonrealDiagonalWeight_measurable m g hg) measurable_const
  simp only [mul_one] at h
  simp_rw [markedNonrealBlockWeight_eq_diagonal m g]
  dsimp only [MarkedNonrealFlagAtlas.source,MarkedNonrealIndex]
  rw [h]
  change F.angleMass k*(∫⁻ d in realSchurMixedDiagonalCodeSource (markedNonrealBlockSizes m) code,
    (ENNReal.ofReal (realSchurMixedDiagonalGaussianJacobian (markedNonrealBlockSizes m) d)*
      markedNonrealDiagonalWeight m g d)*
      (∫⁻ u : RealSchurMixedStrictUpperEntry (markedNonrealBlockSizes m) → ℝ,
        ENNReal.ofReal (Real.exp (-(∑ p, (u p)^2)/2))))=_
  rw [realSchurMixedStrictUpperGaussianLIntegral]
  congr 1
  exact lintegral_mul_const' _ _ ENNReal.ofReal_ne_top

#print axioms MarkedNonrealFlagAtlas.gaussian_fiber
end SpectralRadiusUpperTail
