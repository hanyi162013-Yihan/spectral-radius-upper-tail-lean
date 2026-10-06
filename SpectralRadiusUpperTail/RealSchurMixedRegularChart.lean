import SpectralRadiusUpperTail.RealSchurMixedRegularTangent
import SpectralRadiusUpperTail.RealSchurMixedFullChart
import SpectralRadiusUpperTail.RealSchurMixedOrthogonalTransport
import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Operator

/-- A genuine local mixed real-Schur chart around any matrix with
nonsingular angular orbit determinant, without selecting named canonical
1×1/2×2 representatives. -/
noncomputable def realSchurMixedRegularChart
    {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hdet : (realSchurMixedOrbitMatrix s T).det ≠ 0) :
    OpenPartialHomeomorph (RealSchurMixedTangent s)
      (Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ) :=
  (show HasStrictFDerivAt (realSchurMixedExpCoordinates s T)
      (realSchurMixedTangentEquivOfDet s T hdet :
        RealSchurMixedTangent s →L[ℝ]
          Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ) 0 from
    realSchurMixedExpCoordinates_hasStrictFDerivAt s T).toOpenPartialHomeomorph
      (realSchurMixedExpCoordinates s T)

theorem realSchurMixedRegularChart_zero_mem_source
    {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hdet : (realSchurMixedOrbitMatrix s T).det ≠ 0) :
    0 ∈ (realSchurMixedRegularChart s T hdet).source :=
  (show HasStrictFDerivAt (realSchurMixedExpCoordinates s T)
      (realSchurMixedTangentEquivOfDet s T hdet :
        RealSchurMixedTangent s →L[ℝ]
          Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ) 0 from
    realSchurMixedExpCoordinates_hasStrictFDerivAt s T).mem_toOpenPartialHomeomorph_source

/-- Rotate a regular local chart to an arbitrary orthogonal frame. -/
noncomputable def realSchurMixedRegularRotatedChart
    {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hdet : (realSchurMixedOrbitMatrix s T).det ≠ 0)
    (Q : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hQ : Qᵀ*Q=1) :
    OpenPartialHomeomorph (RealSchurMixedTangent s)
      (Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ) :=
  (realSchurMixedRegularChart s T hdet).transHomeomorph
    (realMatrixOrthogonalConjugationEquiv _ Q hQ).toContinuousLinearEquiv.toHomeomorph

theorem realSchurMixedRegularRotatedChart_center_mem_target
    {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hdet : (realSchurMixedOrbitMatrix s T).det ≠ 0)
    (Q : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hQ : Qᵀ*Q=1) :
    Q*T*Qᵀ ∈ (realSchurMixedRegularRotatedChart s T hdet Q hQ).target := by
  have h0 : 0 ∈ (realSchurMixedRegularRotatedChart s T hdet Q hQ).source :=
    realSchurMixedRegularChart_zero_mem_source s T hdet
  have h := (realSchurMixedRegularRotatedChart s T hdet Q hQ).map_source h0
  change Q*(realSchurMixedExpCoordinates s T 0)*Qᵀ ∈ _ at h
  simpa [realSchurMixedExpCoordinates_zero] using h

#print axioms realSchurMixedRegularRotatedChart_center_mem_target
end SpectralRadiusUpperTail
