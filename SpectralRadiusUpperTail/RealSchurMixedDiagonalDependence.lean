import SpectralRadiusUpperTail.RealSchurMixedGaussianLocalIntegration
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- Each Sylvester factor sees only the two diagonal blocks, never a
strictly upper block. -/
theorem realSchurMixedSylvester_eq_of_diagonal_blocks
    {m : ℕ} (s : Fin m → ℕ)
    (S S' : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hdiag : ∀ i a b, S ⟨i,a⟩ ⟨i,b⟩ = S' ⟨i,a⟩ ⟨i,b⟩)
    (p : RealSchurLowerIndex m) :
    realSchurMixedSylvester s S p =
      realSchurMixedSylvester s S' p := by
  ext r z
  unfold realSchurMixedSylvester
  simp only [hdiag]

/-- The full local Jacobian weight depends on the block-upper matrix
only through its diagonal blocks. -/
theorem realSchurMixedJacobianWeight_eq_of_diagonal_blocks
    {m : ℕ} (s : Fin m → ℕ)
    (T T' : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (x x' : RealSchurMixedTangent s)
    (hangle : x.1=x'.1)
    (hdiag : ∀ i a b,
      (T+x.2.val) ⟨i,a⟩ ⟨i,b⟩ =
      (T'+x'.2.val) ⟨i,a⟩ ⟨i,b⟩) :
    realSchurMixedJacobianWeight s T x =
      realSchurMixedJacobianWeight s T' x' := by
  unfold realSchurMixedJacobianWeight
  rw [hangle]
  congr 1
  apply Finset.prod_congr rfl
  intro p _
  rw [realSchurMixedSylvester_eq_of_diagonal_blocks s _ _ hdiag p]

#print axioms realSchurMixedJacobianWeight_eq_of_diagonal_blocks
end SpectralRadiusUpperTail
