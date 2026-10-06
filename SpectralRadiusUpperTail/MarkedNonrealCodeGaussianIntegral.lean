import SpectralRadiusUpperTail.MarkedNonrealGaussianFiber

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix Matrix.Norms.Operator

theorem MarkedNonrealFlagAtlas.code_gaussian_integral
    {m : ℕ} {hm : 0 < m} (F : MarkedNonrealFlagAtlas m hm)
    (code : MarkedNonrealCode m) (g : ℂ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ y in (realSchurMixedEntryEquiv (markedNonrealBlockSizes m)).symm ⁻¹'
        realSchurMixedCodeClass (markedNonrealBlockSizes m) code,
      ENNReal.ofReal (realSchurMixedGaussianCoordinateWeight (markedNonrealBlockSizes m) y)*
        markedNonrealCodeWeight m ((realSchurMixedEntryEquiv (markedNonrealBlockSizes m)).symm y) code g
      ∂realSchurMixedCoordinateVolume (markedNonrealBlockSizes m)) =
      F.angularMass*(markedNonrealDiagonalCodeIntegral m code g*markedNonrealUpperMass m) := by
  let s := markedNonrealBlockSizes m
  let G := fun y : RealSchurMixedTangent s =>
    markedNonrealCodeWeight m ((realSchurMixedEntryEquiv s).symm y) code g
  have h := realSchurMixedFlagCoded_gaussian_lintegral s (markedNonrealBlockSizes_pos m hm)
    F.marker F.marker_injective F.frames code G
  rw [realSchurMixedCodeClass_chart_image_eq s (markedNonrealBlockSizes_pos m hm)
    F.marker F.marker_injective F.frames F.coverage code] at h
  rw [h]
  have hterm (k : ℕ) :
      (∫⁻ t in F.source k code,
        ENNReal.ofReal (realSchurMixedJacobianWeight s 0 t)*
          (ENNReal.ofReal (realMatrixGaussianWeight (MarkedNonrealIndex m) t.2.val)*G (F.output k t))
        ∂realSchurMixedCoordinateVolume s) =
      F.angleMass k*(markedNonrealDiagonalCodeIntegral m code g*markedNonrealUpperMass m) := by
    calc
      _ = ∫⁻ t in F.source k code,
        ENNReal.ofReal (realSchurMixedJacobianWeight s 0 t)*
          (ENNReal.ofReal (realMatrixGaussianWeight (MarkedNonrealIndex m) t.2.val)*
            markedNonrealBlockWeight (markedNonrealFirstBlock m t.2.val) g)
        ∂realSchurMixedCoordinateVolume s := by
          apply setLIntegral_congr_fun (measurableSet_realSchurMixedFlagCodedSource s
            (markedNonrealBlockSizes_pos m hm) F.marker F.marker_injective F.frames k code)
          intro t ht
          dsimp only
          rw [show G (F.output k t)=markedNonrealBlockWeight (markedNonrealFirstBlock m t.2.val) g
            from F.output_code_weight k code t ht g]
      _ = _ := F.gaussian_fiber k code g hg
  change (∑' k, ∫⁻ t in F.source k code,
    ENNReal.ofReal (realSchurMixedJacobianWeight s 0 t)*
      (ENNReal.ofReal (realMatrixGaussianWeight (MarkedNonrealIndex m) t.2.val)*G (F.output k t))
    ∂realSchurMixedCoordinateVolume s)=_
  simp_rw [hterm]
  exact ENNReal.tsum_mul_right

#print axioms MarkedNonrealFlagAtlas.code_gaussian_integral
end SpectralRadiusUpperTail
