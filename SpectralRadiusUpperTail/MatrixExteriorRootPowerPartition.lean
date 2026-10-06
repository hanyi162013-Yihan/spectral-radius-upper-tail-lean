import SpectralRadiusUpperTail.MatrixExteriorRootPower
import SpectralRadiusUpperTail.MatrixRootExteriorCounts
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

/-- The weighted positive-real part of the exterior root statistic. -/
noncomputable def matrixPositiveRealExteriorPower {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) : ℝ := by
  classical
  exact (A.charpoly.roots.map (fun z : ℂ =>
    if z.im = 0 ∧ 1 < z.re then z.re^(2*k) else 0)).sum

/-- The weighted negative-real part of the exterior root statistic. -/
noncomputable def matrixNegativeRealExteriorPower {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) : ℝ := by
  classical
  exact (A.charpoly.roots.map (fun z : ℂ =>
    if z.im = 0 ∧ z.re < -1 then (-z.re)^(2*k) else 0)).sum

/-- The weighted nonreal part of the exterior root statistic. -/
noncomputable def matrixNonrealExteriorPower {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) : ℝ := by
  classical
  exact (A.charpoly.roots.map (fun z : ℂ =>
    if z.im ≠ 0 ∧ 1 < ‖z‖ then ‖z‖^(2*k) else 0)).sum

private lemma exterior_power_partition_pointwise (z : ℂ) (k : ℕ) :
    (if 1 < ‖z‖ then ‖z‖^(2*k) else 0) =
      (if z.im = 0 ∧ 1 < z.re then z.re^(2*k) else 0) +
      (if z.im = 0 ∧ z.re < -1 then (-z.re)^(2*k) else 0) +
      (if z.im ≠ 0 ∧ 1 < ‖z‖ then ‖z‖^(2*k) else 0) := by
  by_cases him : z.im = 0
  · rw [matrix_real_root_norm z him]
    by_cases hp : 1 < z.re
    · have hn : ¬ z.re < -1 := by linarith
      have habs : |z.re| = z.re := abs_of_pos (by linarith)
      simp [him, hp, hn, habs]
    · by_cases hn : z.re < -1
      · have habs : |z.re| = -z.re := abs_of_neg (by linarith)
        have hnorm : 1 < -z.re := by linarith
        simp [him, hp, hn, habs, hnorm]
      · have habs : |z.re| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
        have hnorm : ¬ 1 < |z.re| := not_lt.mpr habs
        simp [him, hp, hn, hnorm]
  · simp [him]

/-- The exterior root-power statistic splits exactly into the two real
half-lines and the nonreal plane. Multiplicities are preserved. -/
theorem matrixExteriorRootPower_partition {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) :
    matrixExteriorRootPower A k =
      matrixPositiveRealExteriorPower A k +
      matrixNegativeRealExteriorPower A k +
      matrixNonrealExteriorPower A k := by
  classical
  unfold matrixExteriorRootPower matrixPositiveRealExteriorPower
    matrixNegativeRealExteriorPower matrixNonrealExteriorPower
  simp_rw [exterior_power_partition_pointwise]
  simp only [Multiset.sum_map_add]

#print axioms matrixExteriorRootPower_partition
end SpectralRadiusUpperTail
