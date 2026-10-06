import SpectralRadiusUpperTail.RealSchurFixedChartRootCounts
import SpectralRadiusUpperTail.RealGaussianMatrixExplicitDensity
import SpectralRadiusUpperTail.RealSchurMixedGaussianWeight
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix BigOperators

/-- Finite reindexing of the original matrix entries preserves the
Gaussian Frobenius weight exactly. -/
theorem realGaussianMatrixWeight_mixed_reindex
    {n : ℕ} {m : ℕ} {s : Fin m → ℕ}
    (e : Fin n ≃ RealSchurMixedCoord s)
    (x : (Fin n × Fin n) → ℝ) :
    realGaussianMatrixWeight n x =
      realMatrixGaussianWeight (RealSchurMixedCoord s)
        (Matrix.reindex e e (Matrix.of x.curry)) := by
  have hsum :
      (∑ p : Fin n × Fin n, (x p)^2) =
        ∑ q : RealSchurMixedCoord s × RealSchurMixedCoord s,
          ((Matrix.reindex e e (Matrix.of x.curry)) q.1 q.2)^2 := by
    classical
    apply Fintype.sum_equiv (Equiv.prodCongr e e)
    intro p
    simp [Matrix.reindex_apply]
  unfold realGaussianMatrixWeight realMatrixGaussianWeight
  rw [hsum]

#print axioms realGaussianMatrixWeight_mixed_reindex
end SpectralRadiusUpperTail
