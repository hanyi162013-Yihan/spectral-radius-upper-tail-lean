import SpectralRadiusUpperTail.RealPolynomialZeroSets
import SpectralRadiusUpperTail.GaussianMatrixAbsoluteContinuity
import Mathlib.LinearAlgebra.Matrix.Charpoly.Univ
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Matrix

/-- A polynomial in the real matrix entries whose zeros mean that a fixed
real number is a characteristic root. -/
noncomputable def fixedRealEigenvaluePolynomial (n : ℕ) (r : ℝ) :
    MvPolynomial (Fin n × Fin n) ℝ :=
  (Matrix.scalar (Fin n) (MvPolynomial.C r) -
    Matrix.of (fun i j => MvPolynomial.X (i,j))).det

theorem fixedRealEigenvaluePolynomial_eval (n : ℕ) (r : ℝ)
    (x : (Fin n × Fin n) → ℝ) :
    MvPolynomial.eval x (fixedRealEigenvaluePolynomial n r) =
      (Matrix.scalar (Fin n) r - Matrix.of x.curry).det := by
  change (MvPolynomial.eval₂Hom (RingHom.id ℝ) x)
    (fixedRealEigenvaluePolynomial n r) = _
  unfold fixedRealEigenvaluePolynomial
  rw [RingHom.map_det]
  congr 1
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.sub_apply, Matrix.scalar]
  · simp [Matrix.sub_apply, Matrix.scalar, hij]

theorem fixedRealEigenvaluePolynomial_ne_zero (n : ℕ) (r : ℝ) :
    fixedRealEigenvaluePolynomial n r ≠ 0 := by
  let x : (Fin n × Fin n) → ℝ :=
    fun ij => if ij.1 = ij.2 then r+1 else 0
  have hx : Matrix.of x.curry = Matrix.diagonal (fun _ : Fin n => r+1) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [x]
    · simp [x, hij]
  have hdiag : Matrix.scalar (Fin n) r -
      Matrix.diagonal (fun _ : Fin n => r+1) =
      Matrix.diagonal (fun _ : Fin n => (-1 : ℝ)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.scalar]
    · simp [Matrix.scalar, hij]
  have hvalue : MvPolynomial.eval x
      (fixedRealEigenvaluePolynomial n r) ≠ 0 := by
    rw [fixedRealEigenvaluePolynomial_eval, hx, hdiag,
      Matrix.det_diagonal]
    simp
  intro hp
  exact hvalue (by rw [hp, map_zero])

/-- For an actual real Gaussian matrix, any fixed real number is almost
surely not an eigenvalue. This uses only polynomial zero sets and the
Gaussian density, not a Schur or one-point formula. -/
theorem realGaussian_fixed_real_not_eigenvalue_ae (n : ℕ) (r : ℝ) :
    ∀ᵐ x ∂gaussianMatrixLaw n,
      (Matrix.scalar (Fin n) r - Matrix.of x.curry).det ≠ 0 := by
  have hvol : ∀ᵐ x : (Fin n × Fin n) → ℝ
      ∂(volume : Measure ((Fin n × Fin n) → ℝ)),
      MvPolynomial.eval x (fixedRealEigenvaluePolynomial n r) ≠ 0 := by
    simpa only [volume_pi] using
      (mvPolynomial_eval_ne_zero_ae_pi
        (fun _ : Fin n × Fin n => (volume : Measure ℝ))
        (fixedRealEigenvaluePolynomial n r)
        (fixedRealEigenvaluePolynomial_ne_zero n r))
  have hgauss := (gaussianMatrixLaw_absolutelyContinuous_volume n).ae_le hvol
  filter_upwards [hgauss] with x hx
  rwa [fixedRealEigenvaluePolynomial_eval] at hx

#print axioms fixedRealEigenvaluePolynomial_eval
#print axioms fixedRealEigenvaluePolynomial_ne_zero
#print axioms realGaussian_fixed_real_not_eigenvalue_ae
end SpectralRadiusUpperTail
