import SpectralRadiusUpperTail.RealSchurMixedAngularPositive
import SpectralRadiusUpperTail.MarkedRealTwoBlockJacobian
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Operator

/-- A fixed separated two-block center exists in every dimension. Its
marked scalar is zero and its complementary block is the identity. -/
noncomputable def markedRealUnitGapCenter (m : ℕ) :
    Matrix (RealSchurMixedCoord (markedRealTwoBlockSizes m))
      (RealSchurMixedCoord (markedRealTwoBlockSizes m)) ℝ :=
  Matrix.diagonal (fun i => if i.1 = 0 then 0 else 1)

theorem markedRealUnitGapCenter_upper (m : ℕ) :
    realSchurMixedLowerProjection (markedRealTwoBlockSizes m)
      (markedRealUnitGapCenter m) = 0 := by
  apply (realSchurMixed_blockTriangular_iff_lower_zero _ _).mp
  intro a b hba
  have hab : a ≠ b := by
    intro h
    subst b
    exact (lt_irrefl a.1) hba
  simp [markedRealUnitGapCenter, Matrix.diagonal_apply, hab]

theorem markedRealUnitGapCenter_orbit_det (m : ℕ) :
    (realSchurMixedOrbitMatrix (markedRealTwoBlockSizes m)
      (markedRealUnitGapCenter m)).det = 1 := by
  rw [markedRealOrbitMatrix_det m (markedRealUnitGapCenter m)
    1 0]
  · simp
  · intro i j
    simp [markedRealUnitGapCenter, Matrix.diagonal_apply,
      Matrix.one_apply]
  · simp [markedRealUnitGapCenter]

/-- The angular Jacobian is globally continuous in the fixed marked-line
coordinate system, independently of all Schur upper data. -/
theorem markedRealAngularJacobian_continuous (m : ℕ) :
    Continuous (realSchurMixedAngularJacobian
      (markedRealTwoBlockSizes m)) := by
  exact realSchurMixedAngularJacobian_continuous
    (markedRealTwoBlockSizes m) (markedRealUnitGapCenter m)
    (markedRealUnitGapCenter_upper m)
    (by rw [markedRealUnitGapCenter_orbit_det]; norm_num)

#print axioms markedRealAngularJacobian_continuous
end SpectralRadiusUpperTail
