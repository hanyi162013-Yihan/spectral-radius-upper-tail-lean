import SpectralRadiusUpperTail.RealSchurMixedRegularRotatedIntegration
import SpectralRadiusUpperTail.RealSchurMixedGaussianLocalIntegration
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix Matrix.Norms.Operator

theorem realSchurMixedOutputCoordinateEquiv_entry
    {m : ℕ} (s : Fin m → ℕ)
    (Q : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hQ : Qᵀ*Q=1)
    (A : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ) :
    realSchurMixedOutputCoordinateEquiv s Q hQ
      (realSchurMixedEntryEquiv s A) =
        realSchurMixedEntryEquiv s (Q*A*Qᵀ) := by
  simp [realSchurMixedOutputCoordinateEquiv,
    realSchurMixedFlatEntryEquiv, realMatrixOrthogonalEntryEquiv,
    realMatrixOrthogonalConjugationEquiv]

theorem realSchurMixedRotatedEntryCoordinates_eq
    {m : ℕ} (s : Fin m → ℕ)
    (T Q : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hQ : Qᵀ*Q=1) (x : RealSchurMixedTangent s) :
    realSchurMixedRotatedEntryCoordinates s T Q hQ x =
      realSchurMixedEntryEquiv s
        (Q*(realSchurMixedExpCoordinates s T x)*Qᵀ) := by
  exact realSchurMixedOutputCoordinateEquiv_entry s Q hQ
    (realSchurMixedExpCoordinates s T x)

theorem realSchurMixedRegularRotatedChart_apply
    {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hdet : (realSchurMixedOrbitMatrix s T).det ≠ 0)
    (Q : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hQ : Qᵀ*Q=1) (x : RealSchurMixedTangent s) :
    realSchurMixedRegularRotatedChart s T hdet Q hQ x =
      Q*(realSchurMixedExpCoordinates s T x)*Qᵀ := by
  rfl

/-- The Gaussian quadratic density is unchanged under the output
orthogonal rotation in the actual mixed-Schur entry coordinates. -/
theorem realSchurMixedGaussianCoordinateWeight_rotated_chart
    {m : ℕ} (s : Fin m → ℕ)
    (T Q : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hQ : Qᵀ*Q=1) (x : RealSchurMixedTangent s) :
    realSchurMixedGaussianCoordinateWeight s
      (realSchurMixedRotatedEntryCoordinates s T Q hQ x) =
        realMatrixGaussianWeight (RealSchurMixedCoord s) (T+x.2.val) := by
  rw [realSchurMixedRotatedEntryCoordinates,
    realSchurMixedEntryCoordinates,
    realSchurMixedOutputCoordinateEquiv_entry]
  unfold realSchurMixedGaussianCoordinateWeight
  rw [LinearEquiv.symm_apply_apply]
  rw [realMatrixGaussianWeight_orthogonal_conjugation _ Q _ hQ]
  exact realSchurMixedGaussianWeight_chart s T x

/-- The local Gaussian law at any regular mixed real-Schur center and
in any orthogonal frame, with its exact finite-dimensional Jacobian. -/
theorem realSchurMixed_gaussian_lintegral_regular_rotated_chart
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (T Q : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hT : realSchurMixedLowerProjection s T = 0)
    (hdet : (realSchurMixedOrbitMatrix s T).det ≠ 0)
    (hQ : Qᵀ*Q=1)
    (U : Set (RealSchurMixedTangent s))
    (hU : MeasurableSet U)
    (hsub : U ⊆ (realSchurMixedRegularChart s T hdet).source)
    (g : RealSchurMixedTangent s → ℝ≥0∞) :
    ∫⁻ y in realSchurMixedRotatedEntryCoordinates s T Q hQ '' U,
        ENNReal.ofReal (realSchurMixedGaussianCoordinateWeight s y) * g y
        ∂realSchurMixedCoordinateVolume s =
      ∫⁻ x in U,
        ENNReal.ofReal (realSchurMixedJacobianWeight s T x) *
          (ENNReal.ofReal (realMatrixGaussianWeight
            (RealSchurMixedCoord s) (T+x.2.val)) *
            g (realSchurMixedRotatedEntryCoordinates s T Q hQ x))
        ∂realSchurMixedCoordinateVolume s := by
  have h := realSchurMixed_lintegral_regular_rotated_chart
    s hs T Q hT hdet hQ U hU hsub
    (fun y => ENNReal.ofReal (realSchurMixedGaussianCoordinateWeight s y) * g y)
  simpa only [realSchurMixedGaussianCoordinateWeight_rotated_chart] using h

#print axioms realSchurMixed_gaussian_lintegral_regular_rotated_chart
end SpectralRadiusUpperTail
