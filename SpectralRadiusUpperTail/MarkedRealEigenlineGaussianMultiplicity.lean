import SpectralRadiusUpperTail.MarkedRealEigenlineMultiplicity
import SpectralRadiusUpperTail.RealGaussianActualSimpleSpectrum
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory

/-- Under the actual iid real-Gaussian matrix law, every real eigenvalue
almost surely has precisely the two unit-vector marks on its eigenline.
This settles the algebraic multiplicity in the marked-line formula, not its
global Jacobian integration. -/
theorem realGaussian_unit_eigenvector_marks_ae (n : ℕ) :
    ∀ᵐ a : (Fin n × Fin n) → ℝ ∂gaussianMatrixLaw n,
      ∀ (x : ℝ) (v w : EuclideanSpace ℝ (Fin n)),
        ‖v‖ = 1 → ‖w‖ = 1 →
        (Matrix.of a.curry).toEuclideanLin v = x • v →
        (Matrix.of a.curry).toEuclideanLin w = x • w →
        w = v ∨ w = -v := by
  filter_upwards [realGaussianMatrix_charpoly_separable_ae n] with a ha
  intro x v w hv hw hfv hfw
  let f := (Matrix.of a.curry).toEuclideanLin
  have hchar : f.charpoly = (Matrix.of a.curry).charpoly := by
    dsimp [f]
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
    exact Matrix.charpoly_toLin (Matrix.of a.curry)
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have hsep : f.charpoly.Separable := by rw [hchar]; exact ha
  exact real_unit_eigenvectors_eq_or_neg_of_separable
    f hsep x v w hv hw hfv hfw

#print axioms realGaussian_unit_eigenvector_marks_ae
end SpectralRadiusUpperTail
