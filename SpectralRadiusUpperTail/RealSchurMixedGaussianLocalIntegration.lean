import SpectralRadiusUpperTail.RealSchurMixedGaussianWeight
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix Matrix.Norms.Operator

/-- Unnormalized real Gaussian matrix density in the fixed lower/upper
entry coordinates used by the local chart. -/
noncomputable def realSchurMixedGaussianCoordinateWeight
    {m : ℕ} (s : Fin m → ℕ)
    (y : RealSchurMixedTangent s) : ℝ :=
  realMatrixGaussianWeight (RealSchurMixedCoord s)
    ((realSchurMixedEntryEquiv s).symm y)

theorem realSchurMixedGaussianCoordinateWeight_chart
    {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (x : RealSchurMixedTangent s) :
    realSchurMixedGaussianCoordinateWeight s
      (realSchurMixedEntryCoordinates s T x) =
      realMatrixGaussianWeight (RealSchurMixedCoord s) (T+x.2.val) := by
  unfold realSchurMixedGaussianCoordinateWeight realSchurMixedEntryCoordinates
  rw [LinearEquiv.symm_apply_apply]
  exact realSchurMixedGaussianWeight_chart s T x

/-- The actual local Gaussian integral in mixed real-Schur coordinates.
The Gaussian weight is independent of the angular parameter and the
Jacobian is the computed Sylvester product times its angular factor. -/
theorem realSchurMixed_gaussian_lintegral_local_chart
    {m : ℕ} (B : Fin m → RealSchurChartBlock)
    (T : Matrix (RealSchurMixedCoord (fun i => (B i).size))
      (RealSchurMixedCoord (fun i => (B i).size)) ℝ)
    (hT : ∀ a b : Fin m, b < a →
      ∀ x : Fin ((B a).size), ∀ y : Fin ((B b).size),
        T ⟨a,x⟩ ⟨b,y⟩ = 0)
    (hdiag : ∀ i a b, T ⟨i,a⟩ ⟨i,b⟩ = (B i).matrix a b)
    (hsep : ∀ p : RealSchurLowerIndex m,
      realSchurDataSeparated (B p.1.1).data (B p.1.2).data)
    (U : Set (RealSchurMixedTangent (fun i => (B i).size)))
    (hU : MeasurableSet U)
    (hsub : U ⊆ (realSchurMixedLocalChart B T hT hdiag hsep).source)
    (g : RealSchurMixedTangent (fun i => (B i).size) → ℝ≥0∞) :
    ∫⁻ y in realSchurMixedEntryCoordinates (fun i => (B i).size) T '' U,
      ENNReal.ofReal (realSchurMixedGaussianCoordinateWeight
        (fun i => (B i).size) y) * g y
        ∂realSchurMixedCoordinateVolume (fun i => (B i).size) =
      ∫⁻ x in U,
        ENNReal.ofReal (realSchurMixedJacobianWeight
          (fun i => (B i).size) T x) *
          (ENNReal.ofReal (realMatrixGaussianWeight
            (RealSchurMixedCoord (fun i => (B i).size)) (T+x.2.val)) *
            g (realSchurMixedEntryCoordinates (fun i => (B i).size) T x))
        ∂realSchurMixedCoordinateVolume (fun i => (B i).size) := by
  have h := realSchurMixed_lintegral_local_chart B T hT hdiag hsep U hU hsub
    (fun y => ENNReal.ofReal (realSchurMixedGaussianCoordinateWeight
      (fun i => (B i).size) y) * g y)
  simpa only [realSchurMixedGaussianCoordinateWeight_chart] using h

#print axioms realSchurMixed_gaussian_lintegral_local_chart
end SpectralRadiusUpperTail
