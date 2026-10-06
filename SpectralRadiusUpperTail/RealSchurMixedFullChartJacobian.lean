import SpectralRadiusUpperTail.RealSchurMixedFullJacobian
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Operator

/-- The actual exponential-coordinate map, read in fixed lower/upper
matrix-entry coordinates. -/
noncomputable def realSchurMixedEntryCoordinates
    {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (x : RealSchurMixedTangent s) : RealSchurMixedTangent s :=
  realSchurMixedEntryEquiv s (realSchurMixedExpCoordinates s T x)

theorem realSchurMixedEntryCoordinates_hasStrictFDerivAt
    {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ) :
    HasStrictFDerivAt (realSchurMixedEntryCoordinates s T)
      (realSchurMixedCoordinateDifferential s T).toContinuousLinearMap 0 := by
  convert! ((realSchurMixedEntryEquiv s).toContinuousLinearEquiv.hasStrictFDerivAt.comp 0
    (realSchurMixedExpCoordinates_hasStrictFDerivAt s T)) using 1

/-- The determinant is for the genuine full Fréchet derivative of the
local real-Schur map at its center. -/
theorem realSchurMixedEntryCoordinates_fderiv_det
    {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ) :
    (fderiv ℝ (realSchurMixedEntryCoordinates s T) 0).det =
      (realSchurMixedOrbitMatrix s T).det := by
  rw [(realSchurMixedEntryCoordinates_hasStrictFDerivAt s T).hasFDerivAt.fderiv]
  exact realSchurMixedCoordinateDifferential_det s T

/-- Complete local real-Schur Jacobian for arbitrary mixtures of real
scalar blocks and conjugate-pair blocks. Global chart coverage and overlap
multiplicity are separate from this local formula. -/
theorem realSchurMixedEntryCoordinates_fderiv_abs_det
    {m : ℕ} (B : Fin m → RealSchurChartBlock)
    (T : Matrix (RealSchurMixedCoord (fun i => (B i).size))
      (RealSchurMixedCoord (fun i => (B i).size)) ℝ)
    (hT : ∀ a b : Fin m, b < a →
      ∀ x : Fin ((B a).size), ∀ y : Fin ((B b).size),
        T ⟨a,x⟩ ⟨b,y⟩ = 0)
    (hdiag : ∀ i a b, T ⟨i,a⟩ ⟨i,b⟩ = (B i).matrix a b) :
    |(fderiv ℝ (realSchurMixedEntryCoordinates
      (fun i => (B i).size) T) 0).det| =
        ∏ p : RealSchurLowerIndex m,
          realSchurSpectralGap (B p.1.1).data (B p.1.2).data := by
  rw [realSchurMixedEntryCoordinates_fderiv_det]
  exact realSchurChartBlock_orbit_abs_det B T hT hdiag

#print axioms realSchurMixedEntryCoordinates_hasStrictFDerivAt
#print axioms realSchurMixedEntryCoordinates_fderiv_abs_det
end SpectralRadiusUpperTail
