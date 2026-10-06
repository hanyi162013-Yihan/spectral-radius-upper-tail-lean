import SpectralRadiusUpperTail.MarkedRealRankWeights
import SpectralRadiusUpperTail.MarkedRealStereoRankArea
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Classical
open scoped ENNReal Matrix

/-- A complete hemisphere rank layer factors exactly into one angular
mass and one Gaussian upper-matrix integral. This removes all patch
restrictions involving both factors. -/
theorem markedRealStereoRank_gaussian_factor
    (m k : ℕ) (hm : 0 < m) (b : ℝ) :
    (∫⁻ y in
      markedRealStereoEntryMap m ''
        (markedRealStereoSource m ×ˢ
          markedRealUpperRankSource m k b),
      ENNReal.ofReal
        (realSchurMixedGaussianCoordinateWeight
          (markedRealTwoBlockSizes m) y)
        ∂realSchurMixedCoordinateVolume (markedRealTwoBlockSizes m)) =
      (∫⁻ ω, markedRealStereoAngularWeight m ω) *
        (∫⁻ z, markedRealRankRestWeight m k b z) := by
  let s := markedRealTwoBlockSizes m
  let U : Set (RealSchurMixedTangent s) :=
    markedRealStereoSource m ×ˢ markedRealUpperRankSource m k b
  rw [markedRealStereoRank_gaussianArea m k hm b]
  have hU : MeasurableSet U :=
    measurableSet_markedRealStereoRankProduct m k b
  rw [← lintegral_indicator hU]
  have hpoint (x : RealSchurMixedTangent s) :
      U.indicator (fun x =>
        ENNReal.ofReal (
          |(markedRealComplement m x.2.val -
              markedRealScalar m x.2.val •
                (1 : Matrix (Fin m) (Fin m) ℝ)).det| *
            |markedRealStereoAngularJacobian m x.1|) *
          ENNReal.ofReal
            (realMatrixGaussianWeight (RealSchurMixedCoord s) x.2.val)) x =
        markedRealStereoAngularWeight m x.1 *
          markedRealRankRestWeight m k b
            (realSchurMixedUpperEntryEquiv s x.2) := by
    have hsinv : (realSchurMixedUpperEntryEquiv
        (markedRealTwoBlockSizes m)).symm
        (realSchurMixedUpperEntryEquiv s x.2) = x.2 := by
      exact LinearEquiv.symm_apply_apply _ _
    by_cases ha : x.1 ∈ markedRealStereoSource m
    · by_cases hb : x.2 ∈ markedRealUpperRankSource m k b
      · have hx : x ∈ U := ⟨ha,hb⟩
        simp [Set.indicator_of_mem hx,
          markedRealStereoAngularWeight, markedRealRankRestWeight,
          ha, hb, hsinv, ENNReal.ofReal_mul (abs_nonneg _),
          mul_comm, mul_left_comm, mul_assoc]
        rfl
      · have hx : x ∉ U := by
          intro h
          exact hb h.2
        simp [markedRealStereoAngularWeight, markedRealRankRestWeight,
          Set.indicator_of_notMem hx, ha, hb, hsinv]
    · have hx : x ∉ U := by
        intro h
        exact ha h.1
      simp [markedRealStereoAngularWeight, Set.indicator_of_notMem hx, ha]
  have hrewrite :
      (∫⁻ x,
        U.indicator (fun x =>
          ENNReal.ofReal (
            |(markedRealComplement m x.2.val -
                markedRealScalar m x.2.val •
                  (1 : Matrix (Fin m) (Fin m) ℝ)).det| *
              |markedRealStereoAngularJacobian m x.1|) *
            ENNReal.ofReal
              (realMatrixGaussianWeight (RealSchurMixedCoord s) x.2.val)) x
            ∂realSchurMixedCoordinateVolume s) =
        ∫⁻ x, markedRealStereoAngularWeight m x.1 *
          markedRealRankRestWeight m k b
            (realSchurMixedUpperEntryEquiv s x.2)
            ∂realSchurMixedCoordinateVolume s := by
    exact lintegral_congr fun x => hpoint x
  rw [hrewrite]
  exact realSchurMixed_lintegral_angleRest s
    (markedRealStereoAngularWeight m)
    (markedRealRankRestWeight m k b)
    (markedRealStereoAngularWeight_measurable m)
    (markedRealRankRestWeight_measurable m k b)

#print axioms markedRealStereoRank_gaussian_factor
end SpectralRadiusUpperTail
