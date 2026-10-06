import SpectralRadiusUpperTail.MarkedRealTwoBlockFullJacobian
import SpectralRadiusUpperTail.RealSchurMixedRegularGaussianIntegration
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix Matrix.Norms.Operator

/-- The scalar eigenvalue coordinate and complementary matrix in the
marked-line two-block Schur chart. -/
abbrev markedRealScalar (m : ℕ)
    (S : Matrix (RealSchurMixedCoord (markedRealTwoBlockSizes m))
      (RealSchurMixedCoord (markedRealTwoBlockSizes m)) ℝ) : ℝ :=
  S ⟨0, markedRealZeroCoordinate m⟩ ⟨0, markedRealZeroCoordinate m⟩

abbrev markedRealComplement (m : ℕ)
    (S : Matrix (RealSchurMixedCoord (markedRealTwoBlockSizes m))
      (RealSchurMixedCoord (markedRealTwoBlockSizes m)) ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  fun i j => S ⟨1,i⟩ ⟨1,j⟩

theorem markedRealTwoBlock_jacobianWeight
    (m : ℕ) (hm : 0 < m)
    (T : Matrix (RealSchurMixedCoord (markedRealTwoBlockSizes m))
      (RealSchurMixedCoord (markedRealTwoBlockSizes m)) ℝ)
    (hT : realSchurMixedLowerProjection (markedRealTwoBlockSizes m) T = 0)
    (t : RealSchurMixedTangent (markedRealTwoBlockSizes m)) :
    realSchurMixedJacobianWeight (markedRealTwoBlockSizes m) T t =
      |(markedRealComplement m (T+t.2.val) -
          markedRealScalar m (T+t.2.val) •
            (1 : Matrix (Fin m) (Fin m) ℝ)).det| *
        |realSchurMixedAngularJacobian (markedRealTwoBlockSizes m) t.1| := by
  rw [realSchurMixedJacobianWeight_eq_abs_det
    (markedRealTwoBlockSizes m) (by intro i; fin_cases i <;> simp [markedRealTwoBlockSizes, hm])
    T hT t]
  exact markedRealTwoBlock_fderiv_abs_det m T hT t
    (markedRealComplement m (T+t.2.val))
    (markedRealScalar m (T+t.2.val)) (by intros; rfl) rfl

/-- The checked local Gaussian change of variables with the determinant
factor visible. The global marked-line count and its normalization are
separate remaining steps. -/
theorem markedRealTwoBlock_gaussian_lintegral_local
    (m : ℕ) (hm : 0 < m)
    (T Q : Matrix (RealSchurMixedCoord (markedRealTwoBlockSizes m))
      (RealSchurMixedCoord (markedRealTwoBlockSizes m)) ℝ)
    (hT : realSchurMixedLowerProjection (markedRealTwoBlockSizes m) T = 0)
    (hdet : (realSchurMixedOrbitMatrix (markedRealTwoBlockSizes m) T).det ≠ 0)
    (hQ : Qᵀ*Q=1)
    (U : Set (RealSchurMixedTangent (markedRealTwoBlockSizes m)))
    (hU : MeasurableSet U)
    (hsub : U ⊆ (realSchurMixedRegularChart
      (markedRealTwoBlockSizes m) T hdet).source)
    (g : RealSchurMixedTangent (markedRealTwoBlockSizes m) → ℝ≥0∞) :
    ∫⁻ y in realSchurMixedRotatedEntryCoordinates
        (markedRealTwoBlockSizes m) T Q hQ '' U,
      ENNReal.ofReal (realSchurMixedGaussianCoordinateWeight
        (markedRealTwoBlockSizes m) y) * g y
        ∂realSchurMixedCoordinateVolume (markedRealTwoBlockSizes m) =
      ∫⁻ t in U,
        ENNReal.ofReal (
          |(markedRealComplement m (T+t.2.val) -
              markedRealScalar m (T+t.2.val) •
                (1 : Matrix (Fin m) (Fin m) ℝ)).det| *
            |realSchurMixedAngularJacobian (markedRealTwoBlockSizes m) t.1|) *
        (ENNReal.ofReal (realMatrixGaussianWeight
          (RealSchurMixedCoord (markedRealTwoBlockSizes m)) (T+t.2.val)) *
          g (realSchurMixedRotatedEntryCoordinates
            (markedRealTwoBlockSizes m) T Q hQ t))
        ∂realSchurMixedCoordinateVolume (markedRealTwoBlockSizes m) := by
  rw [realSchurMixed_gaussian_lintegral_regular_rotated_chart
    (markedRealTwoBlockSizes m)
    (by intro i; fin_cases i <;> simp [markedRealTwoBlockSizes, hm])
    T Q hT hdet hQ U hU hsub g]
  congr 1
  funext t
  rw [markedRealTwoBlock_jacobianWeight m hm T hT t]

#print axioms markedRealTwoBlock_jacobianWeight
#print axioms markedRealTwoBlock_gaussian_lintegral_local
end SpectralRadiusUpperTail
