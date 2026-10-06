import SpectralRadiusUpperTail.MatrixRadiusEigenvalue
import SpectralRadiusUpperTail.OutlierSpectralRadius
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix.Norms.L2Operator

noncomputable def matrixPositiveRealRootCount {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (r : ℝ) : ℕ := by
  classical
  exact A.charpoly.roots.countP (fun z : ℂ => z.im = 0 ∧ r < z.re)

noncomputable def matrixNegativeRealRootCount {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (r : ℝ) : ℕ := by
  classical
  exact A.charpoly.roots.countP (fun z : ℂ => z.im = 0 ∧ z.re < -r)

noncomputable def matrixNonrealExteriorRootCount {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (r : ℝ) : ℕ := by
  classical
  exact A.charpoly.roots.countP (fun z : ℂ => z.im ≠ 0 ∧ r < ‖z‖)

theorem matrix_root_count_le_dim {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (p : ℂ → Prop) :
    (by classical exact A.charpoly.roots.countP p) ≤ n := by
  classical
  have hcard : A.charpoly.roots.card = n := by
    rw [← (IsAlgClosed.splits A.charpoly).natDegree_eq_card_roots,
      Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  exact (Multiset.countP_le_card (p := p) A.charpoly.roots).trans_eq hcard

theorem matrix_root_count_pos_iff {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (p : ℂ → Prop) :
    0 < (by classical exact A.charpoly.roots.countP p) ↔
      ∃ z ∈ A.charpoly.roots, p z := by
  classical
  exact Multiset.countP_pos

theorem matrix_real_root_norm (z : ℂ) (hz : z.im = 0) :
    ‖z‖ = |z.re| := by
  have he : z = (z.re : ℂ) := Complex.ext (by simp) (by simpa using hz)
  calc
    ‖z‖ = ‖(z.re : ℂ)‖ := congrArg norm he
    _ = |z.re| := by simp

/-- The three root counts are a deterministic partition of the exterior
spectral-radius event. This statement does not require any eigenvalue
measurability or Gaussian law. -/
theorem matrix_radius_exterior_count_cover {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℂ) (r : ℝ) :
    r < (spectralRadius ℂ A).toReal ↔
      0 < matrixPositiveRealRootCount A r ∨
      0 < matrixNegativeRealRootCount A r ∨
      0 < matrixNonrealExteriorRootCount A r := by
  classical
  have hrootSpectrum (z : ℂ) :
      z ∈ A.charpoly.roots ↔ z ∈ spectrum ℂ A := by
    rw [Polynomial.mem_roots A.charpoly_monic.ne_zero]
    exact Matrix.mem_spectrum_iff_isRoot_charpoly.symm
  constructor
  · intro hr
    obtain ⟨z, hz, he⟩ := matrix_radius_eigenvalue hn A
    have hzroot : z ∈ A.charpoly.roots := (hrootSpectrum z).2 hz
    have hzr : r < ‖z‖ := by rw [he]; exact hr
    by_cases him : z.im = 0
    · have hnorm := matrix_real_root_norm z him
      rw [hnorm] at hzr
      rcases le_total 0 z.re with hpos | hneg
      · left
        change 0 < A.charpoly.roots.countP
          (fun z : ℂ => z.im = 0 ∧ r < z.re)
        exact Multiset.countP_pos.mpr
          ⟨z, hzroot, him, by rwa [abs_of_nonneg hpos] at hzr⟩
      · right; left
        change 0 < A.charpoly.roots.countP
          (fun z : ℂ => z.im = 0 ∧ z.re < -r)
        exact Multiset.countP_pos.mpr
          ⟨z, hzroot, him, by rw [abs_of_nonpos hneg] at hzr; linarith⟩
    · right; right
      change 0 < A.charpoly.roots.countP
        (fun z : ℂ => z.im ≠ 0 ∧ r < ‖z‖)
      exact Multiset.countP_pos.mpr ⟨z, hzroot, him, hzr⟩
  · intro h
    rcases h with h | h | h
    · change 0 < A.charpoly.roots.countP
        (fun z : ℂ => z.im = 0 ∧ r < z.re) at h
      obtain ⟨z, hz, him, hzr⟩ := Multiset.countP_pos.mp h
      have hnorm := matrix_real_root_norm z him
      have hzr' : r < ‖z‖ := by rw [hnorm]; exact lt_of_lt_of_le hzr (le_abs_self _)
      exact lt_of_lt_of_le hzr' (complex_eigenvalue_le_spectralRadius A z
        ((hrootSpectrum z).1 hz))
    · change 0 < A.charpoly.roots.countP
        (fun z : ℂ => z.im = 0 ∧ z.re < -r) at h
      obtain ⟨z, hz, him, hzr⟩ := Multiset.countP_pos.mp h
      have hnorm := matrix_real_root_norm z him
      have hzr' : r < ‖z‖ := by rw [hnorm]; exact lt_of_lt_of_le (by linarith) (neg_le_abs z.re)
      exact lt_of_lt_of_le hzr' (complex_eigenvalue_le_spectralRadius A z
        ((hrootSpectrum z).1 hz))
    · change 0 < A.charpoly.roots.countP
        (fun z : ℂ => z.im ≠ 0 ∧ r < ‖z‖) at h
      obtain ⟨z, hz, _, hzr⟩ := Multiset.countP_pos.mp h
      exact lt_of_lt_of_le hzr (complex_eigenvalue_le_spectralRadius A z
        ((hrootSpectrum z).1 hz))

#print axioms matrix_root_count_le_dim
#print axioms matrix_root_count_pos_iff
#print axioms matrix_radius_exterior_count_cover
end SpectralRadiusUpperTail
