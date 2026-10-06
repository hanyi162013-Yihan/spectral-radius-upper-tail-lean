import SpectralRadiusUpperTail.RealMatrixConjugateRoots
import SpectralRadiusUpperTail.MatrixExteriorRootPowerPartition
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

noncomputable def realMatrixUpperNonrealExteriorPower {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) : ℝ := by
  classical
  exact (((A.map Complex.ofRealHom).charpoly.roots).map
    (fun z : ℂ => if 0 < z.im ∧ 1 < ‖z‖ then ‖z‖^(2*k) else 0)).sum

noncomputable def realMatrixLowerNonrealExteriorPower {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) : ℝ := by
  classical
  exact (((A.map Complex.ofRealHom).charpoly.roots).map
    (fun z : ℂ => if z.im < 0 ∧ 1 < ‖z‖ then ‖z‖^(2*k) else 0)).sum

private lemma nonreal_exterior_power_split_pointwise (z : ℂ) (k : ℕ) :
    (if z.im ≠ 0 ∧ 1 < ‖z‖ then ‖z‖^(2*k) else 0) =
      (if 0 < z.im ∧ 1 < ‖z‖ then ‖z‖^(2*k) else 0) +
      (if z.im < 0 ∧ 1 < ‖z‖ then ‖z‖^(2*k) else 0) := by
  by_cases hr : 1 < ‖z‖
  · rcases lt_trichotomy z.im 0 with hm | hm | hm
    · have hne : z.im ≠ 0 := by linarith
      have hp : ¬ 0 < z.im := by linarith
      simp [hr, hm, hne, hp]
    · simp [hm]
    · have hne : z.im ≠ 0 := by linarith
      have hl : ¬ z.im < 0 := by linarith
      simp [hr, hm, hne, hl]
  · simp [hr]

theorem realMatrixNonrealExteriorPower_split {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) :
    matrixNonrealExteriorPower (A.map Complex.ofRealHom) k =
      realMatrixUpperNonrealExteriorPower A k +
      realMatrixLowerNonrealExteriorPower A k := by
  classical
  unfold matrixNonrealExteriorPower realMatrixUpperNonrealExteriorPower
    realMatrixLowerNonrealExteriorPower
  simp_rw [nonreal_exterior_power_split_pointwise]
  simp only [Multiset.sum_map_add]

theorem realMatrixUpperLowerNonrealPower_equal {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) :
    realMatrixUpperNonrealExteriorPower A k =
      realMatrixLowerNonrealExteriorPower A k := by
  classical
  let s := (A.map Complex.ofRealHom).charpoly.roots
  have hs : s.map (starRingEnd ℂ) = s :=
    realMatrix_charpoly_roots_conj A
  have hfun :
      (fun z : ℂ => if 0 < z.im ∧ 1 < ‖z‖ then ‖z‖^(2*k) else 0) ∘
        (starRingEnd ℂ) =
      (fun z : ℂ => if z.im < 0 ∧ 1 < ‖z‖ then ‖z‖^(2*k) else 0) := by
    funext z
    simp [Complex.conj_im]
  unfold realMatrixUpperNonrealExteriorPower
    realMatrixLowerNonrealExteriorPower
  change (s.map (fun z : ℂ => if 0 < z.im ∧ 1 < ‖z‖
    then ‖z‖^(2*k) else 0)).sum =
    (s.map (fun z : ℂ => if z.im < 0 ∧ 1 < ‖z‖
    then ‖z‖^(2*k) else 0)).sum
  calc
    _ = ((s.map (starRingEnd ℂ)).map
        (fun z : ℂ => if 0 < z.im ∧ 1 < ‖z‖
          then ‖z‖^(2*k) else 0)).sum := by rw [hs]
    _ = _ := by simp only [Multiset.map_map, hfun]

/-- The nonreal weighted root sum of a real matrix is exactly twice its
upper-half-plane contribution. -/
theorem realMatrixNonrealExteriorPower_eq_two_upper {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) :
    matrixNonrealExteriorPower (A.map Complex.ofRealHom) k =
      2*realMatrixUpperNonrealExteriorPower A k := by
  rw [realMatrixNonrealExteriorPower_split,
    ← realMatrixUpperLowerNonrealPower_equal]
  ring

#print axioms realMatrixNonrealExteriorPower_split
#print axioms realMatrixUpperLowerNonrealPower_equal
#print axioms realMatrixNonrealExteriorPower_eq_two_upper
end SpectralRadiusUpperTail
