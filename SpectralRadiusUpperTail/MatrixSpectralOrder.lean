import SpectralRadiusUpperTail.MatrixExponentialTraceSpectrum
import Mathlib.Data.Finset.Max

namespace SpectralRadiusUpperTail
open scoped ComplexOrder Matrix MatrixOrder Matrix.Norms.L2Operator
variable {𝕂 : Type*} [RCLike 𝕂] {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
attribute [local instance] matrixL2RealNormedAlgebra

/-- A Hermitian matrix has a maximal real spectral value and is bounded above by it. -/
lemma matrix_exists_spectral_upper_bound {B : Matrix ι ι 𝕂} (hB : B.IsHermitian) :
    ∃ r ∈ spectrum ℝ B, B ≤ algebraMap ℝ (Matrix ι ι 𝕂) r := by
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ hB.eigenvalues Finset.univ_nonempty
  refine ⟨hB.eigenvalues i, hB.eigenvalues_mem_spectrum_real i, ?_⟩
  apply le_algebraMap_of_spectrum_le (ha := (show IsSelfAdjoint B from hB))
  intro r hr
  rw [hB.spectrum_real_eq_range_eigenvalues] at hr
  obtain ⟨j, rfl⟩ := hr
  exact hi j (Finset.mem_univ j)

/-- Semidefinite order controls the upper spectral edge without a chosen eigenvalue ordering. -/
lemma matrix_spectral_order {A B : Matrix ι ι 𝕂}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : A ≤ B)
    {l : ℝ} (hl : l ∈ spectrum ℝ A) : ∃ r ∈ spectrum ℝ B, l ≤ r := by
  obtain ⟨r, hr, hbound⟩ := matrix_exists_spectral_upper_bound hB
  exact ⟨r, hr, (le_algebraMap_iff_spectrum_le
    (show IsSelfAdjoint A from hA)).mp (hAB.trans hbound) l hl⟩

/-- A deterministic operator-norm bound gives a scalar semidefinite upper bound. -/
lemma matrix_le_scalar_of_norm {D : Matrix ι ι 𝕂} (hD : D.IsHermitian)
    {v : ℝ} (hv : ‖D‖ ≤ v) : D ≤ algebraMap ℝ (Matrix ι ι 𝕂) v := by
  apply le_algebraMap_of_spectrum_le (ha := (show IsSelfAdjoint D from hD))
  intro r hr
  exact (Real.le_norm_self r).trans ((spectrum.norm_le_norm_of_mem hr).trans hv)

#print axioms matrix_exists_spectral_upper_bound
#print axioms matrix_spectral_order
#print axioms matrix_le_scalar_of_norm
end SpectralRadiusUpperTail
