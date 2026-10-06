import SpectralRadiusUpperTail.MarkedRealAngularGaussianKernel
import SpectralRadiusUpperTail.MarkedRealKernelCharpoly
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix BigOperators

/-- The explicit unnormalized Gaussian characteristic-polynomial kernel
remaining after the local angular integration. -/
noncomputable def markedRealCharpolyKernel
    (m : ℕ) (b : ℝ) (x : ℝ) (a : (Fin m × Fin m) → ℝ) : ℝ≥0∞ :=
  if b < x then
    ENNReal.ofReal |(Matrix.of a.curry).charpoly.eval x| *
      (ENNReal.ofReal
        (Real.exp (-(x^2 + ∑ ij : Fin m × Fin m, (a ij)^2)/2)) *
        ENNReal.ofReal ((Real.sqrt (2*Real.pi)) ^
          (Fintype.card
            (RealSchurMixedStrictUpperEntry (markedRealTwoBlockSizes m)))))
  else 0

theorem markedRealNoSpectrumDiagonalWeight_eq_charpoly
    (m : ℕ) (b x : ℝ) (a : (Fin m × Fin m) → ℝ) :
    markedRealNoSpectrumDiagonalWeight m b (x,a) =
      markedRealCharpolyKernel m b x a := by
  unfold markedRealNoSpectrumDiagonalWeight markedRealCharpolyKernel
  by_cases hb : b < x
  · simp only [if_pos hb]
    rw [markedReal_abs_det_sub_scalar_eq_charpoly]
  · simp only [if_neg hb]

/-- Every rank layer on one fixed angular chart combines into an
iterated scalar/complement characteristic-polynomial integral. -/
theorem markedRealAngularRank_gaussian_area_tsum_charpoly
    (m : ℕ) (hm : 0 < m) (b : ℝ) :
    (∑' k : ℕ,
      ∫⁻ y in
        realSchurMixedEntryCoordinates (markedRealTwoBlockSizes m) 0 ''
          (markedRealAngularPositiveSource m ×ˢ
            markedRealUpperRankSource m k b),
        ENNReal.ofReal
          (realSchurMixedGaussianCoordinateWeight
            (markedRealTwoBlockSizes m) y)
          ∂realSchurMixedCoordinateVolume (markedRealTwoBlockSizes m)) =
      (∫⁻ ω, markedRealAngularWeight m ω) *
        (∫⁻ x : ℝ, ∫⁻ a : (Fin m × Fin m) → ℝ,
          markedRealCharpolyKernel m b x a) := by
  rw [markedRealAngularRank_gaussian_area_tsum_kernel m hm b,
    markedRealNoSpectrumDiagonalWeight_lintegral_prod m b]
  congr 1
  apply lintegral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    apply lintegral_congr_ae
    exact Filter.Eventually.of_forall
      (markedRealNoSpectrumDiagonalWeight_eq_charpoly m b x))

#print axioms markedRealAngularRank_gaussian_area_tsum_charpoly
end SpectralRadiusUpperTail
