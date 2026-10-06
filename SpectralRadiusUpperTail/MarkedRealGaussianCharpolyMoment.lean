import SpectralRadiusUpperTail.MarkedRealAngularCharpolyKernel
import SpectralRadiusUpperTail.MarkedRealGaussianDeterminantLIntegral
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix BigOperators

/-- Actual iid-Gaussian absolute characteristic-polynomial moment, in
nonnegative-integral form. -/
noncomputable def markedRealGaussianCharpolyMoment
    (m : ℕ) (x : ℝ) : ℝ≥0∞ :=
  ∫⁻ a : (Fin m × Fin m) → ℝ,
    ENNReal.ofReal |(Matrix.of a.curry).charpoly.eval x|
      ∂Measure.pi (fun _ => standardNormal)

/-- The local complementary-matrix integral is the actual Gaussian
determinant moment times explicit scalar and Gaussian normalizers. -/
theorem markedRealCharpolyKernel_lintegral_complement
    (m : ℕ) (b x : ℝ) :
    (∫⁻ a : (Fin m × Fin m) → ℝ,
      markedRealCharpolyKernel m b x a) =
      if b < x then
        ENNReal.ofReal (Real.exp (-x^2/2)) *
          ENNReal.ofReal ((Real.sqrt (2*Real.pi)) ^
            (Fintype.card
              (RealSchurMixedStrictUpperEntry (markedRealTwoBlockSizes m)))) *
          ENNReal.ofReal ((Real.sqrt (2*Real.pi))^(m^2)) *
          markedRealGaussianCharpolyMoment m x
      else 0 := by
  by_cases hb : b < x
  · rw [if_pos hb]
    have hpoint (a : (Fin m × Fin m) → ℝ) :
        markedRealCharpolyKernel m b x a =
          (ENNReal.ofReal (Real.exp (-x^2/2)) *
            ENNReal.ofReal ((Real.sqrt (2*Real.pi)) ^
              (Fintype.card
                (RealSchurMixedStrictUpperEntry (markedRealTwoBlockSizes m))))) *
          (ENNReal.ofReal (realGaussianArrayWeight (Fin m) a) *
            ENNReal.ofReal |(Matrix.of a.curry).charpoly.eval x|) := by
      unfold markedRealCharpolyKernel
      rw [if_pos hb]
      have hExp :
          Real.exp (-(x^2 + ∑ ij : Fin m × Fin m, (a ij)^2)/2) =
            Real.exp (-x^2/2) *
              realGaussianArrayWeight (Fin m) a := by
        unfold realGaussianArrayWeight
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hExp, ENNReal.ofReal_mul (Real.exp_pos _).le]
      ac_rfl
    simp_rw [hpoint]
    rw [lintegral_const_mul']
    · rw [markedReal_gaussianDeterminant_lintegral]
      change _ = _ * _ * _ * markedRealGaussianCharpolyMoment m x
      ac_rfl
    · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        ENNReal.ofReal_ne_top
  · simp [markedRealCharpolyKernel, hb]

#print axioms markedRealCharpolyKernel_lintegral_complement
end SpectralRadiusUpperTail
