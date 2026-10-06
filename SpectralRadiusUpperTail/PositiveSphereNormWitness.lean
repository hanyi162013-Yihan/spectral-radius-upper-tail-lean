import SpectralRadiusUpperTail.PositiveDiagonalSphereBound
import SpectralRadiusUpperTail.GramMaximumEnergy
import SpectralRadiusUpperTail.HaarSphereIsometry

namespace SpectralRadiusUpperTail
open MeasureTheory Metric
open scoped ENNReal BigOperators ComplexOrder MatrixOrder

noncomputable def complexSpherePositiveMoment (n : ℕ) (a : ℝ)
    (A : Matrix (Fin n) (Fin n) ℂ) : ℝ≥0∞ :=
  ∫⁻ v : sphere (0 : EuclideanSpace ℂ (Fin n)) 1,
    ENNReal.ofReal (Real.exp (a*‖Matrix.toEuclideanCLM (𝕜 := ℂ) A v.val‖^2))
    ∂haarSphereProbability (volume : Measure (EuclideanSpace ℂ (Fin n)))

lemma complex_positive_sphere_diagonalization (n : ℕ) (hn : 0 < n) (a : ℝ)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    complexSpherePositiveMoment n a A = complexDiagonalSphereIntegral n (-a)
      (Matrix.posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let H := (Matrix.posSemidef_conjTranspose_mul_self A).isHermitian
  let F : EuclideanSpace ℂ (Fin n) → ℝ≥0∞ := fun v =>
    ENNReal.ofReal (Real.exp (a*‖Matrix.toEuclideanCLM (𝕜 := ℂ) A v‖^2))
  have hF : Measurable F := by dsimp [F]; fun_prop
  let U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n) :=
    { H.eigenvectorBasis.repr.symm.toLinearEquiv.restrictScalars ℝ with
      norm_map' := H.eigenvectorBasis.repr.symm.norm_map }
  have he := haarSphere_lintegral_isometry U F hF
  change (∫⁻ v : sphere (0 : EuclideanSpace ℂ (Fin n)) 1,
    F v.val ∂haarSphereProbability (volume : Measure (EuclideanSpace ℂ (Fin n)))) = _
  rw [← he]
  apply lintegral_congr
  intro v
  have hg : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A (U v.val)‖^2 =
      ∑ i, H.eigenvalues i*‖v.val i‖^2 := by
    have he' := hermitian_eigenbasis_energy (A.conjTranspose*A) H v.val
    have hgram := matrix_gram_energy A (H.eigenvectorBasis.repr.symm v.val)
    convert! hgram.symm.trans he' using 1
  change ENNReal.ofReal (Real.exp (a*‖Matrix.toEuclideanCLM (𝕜 := ℂ) A (U v.val)‖^2)) = _
  rw [hg]
  simp only [neg_neg]

lemma complex_sphere_positive_norm_witness (n : ℕ) (hn : 0 < n) (a : ℝ) (ha : 0 ≤ a)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    (1/2 : ℝ≥0∞)*ENNReal.ofReal
      (Real.exp (a*‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖^2/2-2*(n : ℝ))) ≤
        complexSpherePositiveMoment n a A := by
  obtain ⟨i, hi⟩ := gram_exists_maximum hn A
  rw [complex_positive_sphere_diagonalization n hn]
  apply le_trans ?_ (complex_positive_diagonal_sphere_lower n hn i a ha _ (fun j => by
    rw [gram_eigenvalue_energy]; positivity))
  apply mul_le_mul' le_rfl
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  linarith [mul_le_mul_of_nonneg_left hi ha]

#print axioms complexSpherePositiveMoment
#print axioms complex_positive_sphere_diagonalization
#print axioms complex_sphere_positive_norm_witness
end SpectralRadiusUpperTail
