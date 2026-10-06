import SpectralRadiusUpperTail.MarkedRealStereoLineDerivative
import SpectralRadiusUpperTail.MarkedRealStereoSmooth
import SpectralRadiusUpperTail.RealMatrixEntryDifferential

namespace SpectralRadiusUpperTail
open scoped Matrix BigOperators Matrix.Norms.Operator

theorem markedRealStereoFrame_fderiv_first_first
    (m : ℕ) (u h : Fin m → ℝ) :
    (fderiv ℝ (markedRealStereoFrame m) u h)
      (markedRealFirstCoordinate m) (markedRealFirstCoordinate m) =
      -4*(u ⬝ᵥ h)/(markedRealStereoDenom m u)^2 := by
  exact (realMatrixEntry_line_hasDerivAt (markedRealStereoFrame m) u h
    (markedRealStereoFrame_differentiable m u)
    (markedRealFirstCoordinate m) (markedRealFirstCoordinate m)).unique
      (markedRealStereoFrame_first_line_hasDerivAt m u h)

theorem markedRealStereoFrame_fderiv_complement_first
    (m : ℕ) (u h : Fin m → ℝ) (i : Fin m) :
    (fderiv ℝ (markedRealStereoFrame m) u h) ⟨1,i⟩ (markedRealFirstCoordinate m) =
      2*h i/markedRealStereoDenom m u -
        4*u i*(u ⬝ᵥ h)/(markedRealStereoDenom m u)^2 := by
  exact (realMatrixEntry_line_hasDerivAt (markedRealStereoFrame m) u h
    (markedRealStereoFrame_differentiable m u) ⟨1,i⟩ (markedRealFirstCoordinate m)).unique
      (markedRealStereoFrame_complement_line_hasDerivAt m u h i)

#print axioms markedRealStereoFrame_fderiv_first_first
#print axioms markedRealStereoFrame_fderiv_complement_first
end SpectralRadiusUpperTail
