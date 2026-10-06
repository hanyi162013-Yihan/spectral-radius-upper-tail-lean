import SpectralRadiusUpperTail.RealSchurMixedLocalIntegration
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix BigOperators

/-- Unnormalized Gaussian density on a real matrix with an arbitrary
finite row and column index. -/
noncomputable def realMatrixGaussianWeight (ι : Type*) [Fintype ι]
    (A : Matrix ι ι ℝ) : ℝ :=
  Real.exp (-(∑ p : ι × ι, (A p.1 p.2)^2)/2)

theorem realMatrix_sum_squares_eq_trace
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) :
    (∑ p : ι × ι, (A p.1 p.2)^2) = (A*Aᵀ).trace := by
  simp only [Fintype.sum_prod_type, Matrix.trace,
    Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Orthogonal conjugation preserves the exact Gaussian quadratic
weight in arbitrary mixed-block coordinates. -/
theorem realMatrixGaussianWeight_orthogonal_conjugation
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (Q S : Matrix ι ι ℝ) (hQ : Qᵀ*Q=1) :
    realMatrixGaussianWeight ι (Q*S*Qᵀ) =
      realMatrixGaussianWeight ι S := by
  have hprod : (Q*S*Qᵀ)*(Q*S*Qᵀ)ᵀ = Q*(S*Sᵀ)*Qᵀ := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Qᵀ Q, hQ]
    simp only [Matrix.one_mul]
  have htrace : ((Q*S*Qᵀ)*(Q*S*Qᵀ)ᵀ).trace =
      (S*Sᵀ).trace := by
    rw [hprod, Matrix.trace_mul_cycle]
    simp only [hQ, Matrix.one_mul]
  unfold realMatrixGaussianWeight
  rw [realMatrix_sum_squares_eq_trace,
    realMatrix_sum_squares_eq_trace, htrace]

/-- In the actual mixed real-Schur chart, the Gaussian density depends
on the block-upper matrix and is independent of the angular parameter. -/
theorem realSchurMixedGaussianWeight_chart
    {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (x : RealSchurMixedTangent s) :
    realMatrixGaussianWeight (RealSchurMixedCoord s)
      (realSchurMixedExpCoordinates s T x) =
    realMatrixGaussianWeight (RealSchurMixedCoord s) (T+x.2.val) := by
  rw [realSchurMixedExpCoordinates_eq_conjugation]
  exact realMatrixGaussianWeight_orthogonal_conjugation
    (RealSchurMixedCoord s) (realSchurMixedAngularFrame s x.1)
    (T+x.2.val) (realSchurMixedAngularFrame_orthogonal s x.1)

#print axioms realMatrixGaussianWeight_orthogonal_conjugation
#print axioms realSchurMixedGaussianWeight_chart
end SpectralRadiusUpperTail
