import SpectralRadiusUpperTail.MatrixExteriorRootPowerPartition
import SpectralRadiusUpperTail.RealMatrixNonrealPairPower
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

theorem matrixPositiveRealExteriorPower_nonneg_le_total
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) :
    0 ≤ matrixPositiveRealExteriorPower A k ∧
      matrixPositiveRealExteriorPower A k ≤ matrixExteriorRootPower A k := by
  classical
  let wp : ℂ → ℝ := fun z =>
    if z.im = 0 ∧ 1 < z.re then z.re^(2*k) else 0
  let wt : ℂ → ℝ := fun z =>
    if 1 < ‖z‖ then ‖z‖^(2*k) else 0
  have hp0 (z : ℂ) : 0 ≤ wp z := by
    by_cases hp : z.im = 0 ∧ 1 < z.re
    · simpa [wp, hp] using
        (pow_nonneg (le_of_lt (lt_trans zero_lt_one hp.2)) (2*k))
    · simp [wp, hp]
  have hpt (z : ℂ) : wp z ≤ wt z := by
    by_cases hp : z.im = 0 ∧ 1 < z.re
    · have hnorm : ‖z‖ = z.re := by
        rw [matrix_real_root_norm z hp.1,
          abs_of_pos (by linarith [hp.2])]
      have hr : 1 < ‖z‖ := by rw [hnorm]; exact hp.2
      simp [wp, wt, hp, hnorm]
    · have ht0 : 0 ≤ wt z := by
        dsimp [wt]
        split_ifs <;> positivity
      simpa [wp, hp] using ht0
  constructor
  · have h := Multiset.sum_map_le_sum_map (s := A.charpoly.roots)
      (fun _ => (0 : ℝ)) wp (fun z _ => hp0 z)
    simpa [matrixPositiveRealExteriorPower, wp] using h
  · have h := Multiset.sum_map_le_sum_map (s := A.charpoly.roots)
      wp wt (fun z _ => hpt z)
    simpa [matrixPositiveRealExteriorPower, matrixExteriorRootPower,
      wp, wt] using h

theorem realMatrixUpperNonrealExteriorPower_nonneg_le_total
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) :
    0 ≤ realMatrixUpperNonrealExteriorPower A k ∧
      realMatrixUpperNonrealExteriorPower A k ≤
        matrixExteriorRootPower (A.map Complex.ofRealHom) k := by
  classical
  let wu : ℂ → ℝ := fun z =>
    if 0 < z.im ∧ 1 < ‖z‖ then ‖z‖^(2*k) else 0
  let wt : ℂ → ℝ := fun z =>
    if 1 < ‖z‖ then ‖z‖^(2*k) else 0
  have hu0 (z : ℂ) : 0 ≤ wu z := by
    dsimp [wu]
    split_ifs <;> positivity
  have hut (z : ℂ) : wu z ≤ wt z := by
    by_cases hu : 0 < z.im ∧ 1 < ‖z‖
    · simp [wu, wt, hu]
    · have ht0 : 0 ≤ wt z := by
        dsimp [wt]
        split_ifs <;> positivity
      simpa [wu, hu] using ht0
  constructor
  · have h := Multiset.sum_map_le_sum_map
      (s := (A.map Complex.ofRealHom).charpoly.roots)
      (fun _ => (0 : ℝ)) wu (fun z _ => hu0 z)
    simpa [realMatrixUpperNonrealExteriorPower, wu] using h
  · have h := Multiset.sum_map_le_sum_map
      (s := (A.map Complex.ofRealHom).charpoly.roots)
      wu wt (fun z _ => hut z)
    simpa [realMatrixUpperNonrealExteriorPower,
      matrixExteriorRootPower, wu, wt] using h

#print axioms matrixPositiveRealExteriorPower_nonneg_le_total
#print axioms realMatrixUpperNonrealExteriorPower_nonneg_le_total
end SpectralRadiusUpperTail
