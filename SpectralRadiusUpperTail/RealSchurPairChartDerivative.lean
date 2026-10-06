import SpectralRadiusUpperTail.RealSchurPairChartEquiv
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open ContinuousLinearMap

/-- Fréchet derivative of the polynomial pair-coordinate map. -/
noncomputable def realSchurPairChartLinear (b c : ℝ) :
    (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (c • fst ℝ ℝ ℝ + b • snd ℝ ℝ ℝ).prod
    ((2*(b-c)) • fst ℝ ℝ ℝ - (2*(b-c)) • snd ℝ ℝ ℝ)

theorem realSchurPairChartLinear_apply (b c h k : ℝ) :
    realSchurPairChartLinear b c (h,k) =
      (c*h+b*k, 2*(b-c)*(h-k)) := by
  simp [realSchurPairChartLinear]
  ring

theorem realSchurPairCoordinates_hasFDerivAt (b c : ℝ) :
    HasFDerivAt
      (fun p : ℝ × ℝ => realSchurPairCoordinates p.1 p.2)
      (realSchurPairChartLinear b c) (b,c) := by
  have hf : HasFDerivAt (fun p : ℝ × ℝ => p.1)
      (fst ℝ ℝ ℝ) (b,c) := hasFDerivAt_fst
  have hg : HasFDerivAt (fun p : ℝ × ℝ => p.2)
      (snd ℝ ℝ ℝ) (b,c) := hasFDerivAt_snd
  have h := (hf.mul hg).prodMk ((hf.sub hg).pow 2)
  convert h using 1 <;> try rfl
  apply ContinuousLinearMap.ext
  intro p
  rcases p with ⟨u,v⟩
  simp [realSchurPairChartLinear, ContinuousLinearMap.prod_apply]
  constructor <;> ring

theorem realSchurPairChartLinear_toMatrix (b c : ℝ) :
    LinearMap.toMatrix (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ)
      (realSchurPairChartLinear b c).toLinearMap =
        realSchurPairCoordinateDerivative b c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [LinearMap.toMatrix_apply, realSchurPairCoordinateDerivative,
      realSchurPairChartLinear_apply, Module.Basis.finTwoProd_zero,
      Module.Basis.finTwoProd_one]

theorem realSchurPairChartLinear_det (b c : ℝ) :
    (realSchurPairChartLinear b c).det = -2*(b-c)*(b+c) := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ)]
  rw [realSchurPairChartLinear_toMatrix,
    realSchur_pair_coordinate_derivative_det]

#print axioms realSchurPairChartLinear_apply
#print axioms realSchurPairCoordinates_hasFDerivAt
#print axioms realSchurPairChartLinear_toMatrix
#print axioms realSchurPairChartLinear_det
end SpectralRadiusUpperTail
