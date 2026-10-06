import SpectralRadiusUpperTail.RealSchurComplexEigenplane
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- A complex eigenvector with real eigenvalue yields an actual nonzero
real eigenvector by taking whichever component is nonzero. -/
theorem realMatrix_realComplexEigenvalue_hasRealEigenvector
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (z : Fin n → ℂ) (ζ : ℂ)
    (hz : (A.map Complex.ofRealHom).mulVec z = ζ • z)
    (hz0 : z ≠ 0) (hIm : ζ.im = 0) :
    ∃ u : Fin n → ℝ, u ≠ 0 ∧ A.mulVec u = ζ.re • u := by
  let u : Fin n → ℝ := fun i => (z i).re
  let v : Fin n → ℝ := fun i => (z i).im
  have hpair := realMatrix_complexEigenvector_re_im A z ζ hz
  change A.mulVec u = ζ.re • u - ζ.im • v ∧
    A.mulVec v = ζ.im • u + ζ.re • v at hpair
  have huEq : A.mulVec u = ζ.re • u := by simpa [hIm] using hpair.1
  have hvEq : A.mulVec v = ζ.re • v := by simpa [hIm] using hpair.2
  by_cases hu : u = 0
  · have hv : v ≠ 0 := by
      intro hv0
      apply hz0
      funext i
      apply Complex.ext
      · simpa [u] using congrFun hu i
      · simpa [v] using congrFun hv0 i
    exact ⟨v,hv,hvEq⟩
  · exact ⟨u,hu,huEq⟩

#print axioms realMatrix_realComplexEigenvalue_hasRealEigenvector
end SpectralRadiusUpperTail
