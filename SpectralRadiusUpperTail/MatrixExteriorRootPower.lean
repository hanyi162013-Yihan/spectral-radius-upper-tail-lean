import SpectralRadiusUpperTail.MatrixRadiusEigenvalue
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix.Norms.L2Operator

/-- Sum of the radial powers of characteristic-polynomial roots outside
the unit disk, counted with algebraic multiplicity. -/
noncomputable def matrixExteriorRootPower {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) : ℝ := by
  classical
  exact (A.charpoly.roots.map
    (fun z : ℂ => if 1 < ‖z‖ then ‖z‖^(2*k) else 0)).sum

theorem matrixExteriorRootPower_nonneg {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) :
    0 ≤ matrixExteriorRootPower A k := by
  classical
  let w : ℂ → ℝ := fun z => if 1 < ‖z‖ then ‖z‖^(2*k) else 0
  have hw (z : ℂ) : 0 ≤ w z := by
    dsimp [w]
    split_ifs <;> positivity
  have hlist : ∀ t ∈ (A.charpoly.roots.map w).toList, 0 ≤ t := by
    intro t ht
    have ht' : t ∈ A.charpoly.roots.map w := by simpa using ht
    obtain ⟨z, _, rfl⟩ := Multiset.mem_map.mp ht'
    exact hw z
  have hs := List.sum_nonneg hlist
  rw [Multiset.sum_toList] at hs
  simpa only [matrixExteriorRootPower, w] using hs

/-- One root attaining the spectral radius is already enough to control
the clipped radius power by the total exterior root-power sum. -/
theorem matrix_clipped_radius_power_le_exterior_sum {n : ℕ}
    (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) :
    (max 1 (spectralRadius ℂ A).toReal)^(2*k) ≤
      1+matrixExteriorRootPower A k := by
  classical
  let R : ℝ := (spectralRadius ℂ A).toReal
  let w : ℂ → ℝ := fun z => if 1 < ‖z‖ then ‖z‖^(2*k) else 0
  have hw (z : ℂ) : 0 ≤ w z := by
    dsimp [w]
    split_ifs <;> positivity
  by_cases hR : R ≤ 1
  · rw [max_eq_left hR]
    have hsum := matrixExteriorRootPower_nonneg A k
    simp only [one_pow]
    linarith
  · have hR' : 1 < R := lt_of_not_ge hR
    obtain ⟨z, hz, hzr⟩ := matrix_radius_eigenvalue hn A
    have hroot : z ∈ A.charpoly.roots := by
      rw [Polynomial.mem_roots A.charpoly_monic.ne_zero]
      exact Matrix.mem_spectrum_iff_isRoot_charpoly.mp hz
    have hwz : w z = R^(2*k) := by
      dsimp [w]
      rw [if_pos (by rwa [hzr])]
      rw [hzr]
    have hlist : ∀ t ∈ (A.charpoly.roots.map w).toList, 0 ≤ t := by
      intro t ht
      have ht' : t ∈ A.charpoly.roots.map w := by simpa using ht
      obtain ⟨u, _, rfl⟩ := Multiset.mem_map.mp ht'
      exact hw u
    have hmem : w z ∈ (A.charpoly.roots.map w).toList := by
      have hm : w z ∈ A.charpoly.roots.map w :=
        Multiset.mem_map.mpr ⟨z, hroot, rfl⟩
      simpa using hm
    have hle : w z ≤ matrixExteriorRootPower A k := by
      have hh := List.single_le_sum hlist (w z) hmem
      rw [Multiset.sum_toList] at hh
      simpa only [matrixExteriorRootPower, w] using hh
    rw [max_eq_right hR'.le]
    rw [hwz] at hle
    linarith

#print axioms matrixExteriorRootPower_nonneg
#print axioms matrix_clipped_radius_power_le_exterior_sum
end SpectralRadiusUpperTail
