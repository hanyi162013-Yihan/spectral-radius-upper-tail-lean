import SpectralRadiusUpperTail.MarkedRealFixedRootRegularFrame
import SpectralRadiusUpperTail.RealGaussianActualSimpleSpectrum
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Matrix

/-- Under the actual iid real-Gaussian law, every real characteristic
root almost surely has a nonsingular two-block Schur chart. This is
pointwise chart coverage, not yet the global one-point density formula. -/
theorem realGaussian_every_real_root_has_regular_frame
    (m : ℕ) (hm : 0 < m) :
    ∀ᵐ a : (Fin (m+1) × Fin (m+1)) → ℝ ∂gaussianMatrixLaw (m+1),
      ∀ x : ℝ,
        (Matrix.of a.curry).charpoly.IsRoot x →
          ∃ e : Fin (m+1) ≃ RealSchurMixedCoord (markedRealTwoBlockSizes m),
          ∃ c : RealSchurMixedRegularFrame (markedRealTwoBlockSizes m),
            markedRealScalar m c.T = x ∧
              Matrix.reindex e e (Matrix.of a.curry) = c.Q * c.T * c.Qᵀ := by
  filter_upwards [realGaussianMatrix_charpoly_separable_ae (m+1)] with a ha
  intro x hx
  exact exists_fixedRealRoot_regular_frame m hm (Matrix.of a.curry) ha x hx

#print axioms realGaussian_every_real_root_has_regular_frame
end SpectralRadiusUpperTail
