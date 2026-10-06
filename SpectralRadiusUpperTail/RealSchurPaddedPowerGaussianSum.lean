import SpectralRadiusUpperTail.RealSchurFixedStartGaussianAll
import SpectralRadiusUpperTail.RealSchurFixedStartFamily
import SpectralRadiusUpperTail.RealSchurPaddedPathExpansion

namespace SpectralRadiusUpperTail
open scoped BigOperators

/-- One block of a padded Schur power as a sum over all increasing paths
with the prescribed start and terminal block. -/
noncomputable def realSchurBlockPowerPathSum {N : ℕ} (n k : ℕ)
    (B : Fin N → RealSchurBlockData)
    (i j : Fin N)
    (z : (Fin N → ℝ) × (SchurEntryIndex N 2 → ℝ)) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  ∑ p : SchurFixedStartFiniteFamily N k i,
    if anyPathLast (schurFixedStartFinitePath p) = j then
      realSchurGlobalWaitingSum n k B (schurFixedStartFinitePath p) z else 0

theorem realSchurPaddedPower_gaussian_sum {N : ℕ} (n k : ℕ) (hk : 0 < k)
    (B : Fin N → RealSchurBlockData)
    (z : (Fin N → ℝ) × (SchurEntryIndex N 2 → ℝ))
    (i j : Fin N) :
    ((realSchurPaddedMatrix n B z)^k) i j =
      realSchurBlockPowerPathSum n k B i j z := by
  rw [realSchurPaddedPower_strict_path_sum]
  unfold realSchurBlockPowerPathSum
  rw [← Fin.sum_univ_eq_sum_range, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro l hl
  refine (realSchurFixedStartPathSum_gaussian_all n k l.val hk B z i j).trans ?_
  apply Finset.sum_congr
  · ext p
    simp
  · intro p hp
    rfl

#print axioms realSchurPaddedPower_gaussian_sum
end SpectralRadiusUpperTail
