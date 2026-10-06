import SpectralRadiusUpperTail.ComplexAnnulusCover
import SpectralRadiusUpperTail.MatrixRadiusEigenvalue
import SpectralRadiusUpperTail.ComplexWitnessMarkov

namespace SpectralRadiusUpperTail

lemma matrix_annulus_approximate_vector (r R δ : ℝ) (S : Finset ℂ)
    (hcover : ∀ w : ℂ, r ≤ ‖w‖ → ‖w‖ ≤ R → ∃ z ∈ S, ‖w-z‖ < δ)
    (n : ℕ) (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℂ)
    (hr : r ≤ (spectralRadius ℂ A).toReal)
    (hR : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ ≤ R) :
    ∃ z ∈ S, ∃ v : EuclideanSpace ℂ (Fin n), ‖v‖ = 1 ∧
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A-z • 1) v‖^2 ≤ δ^2 := by
  obtain ⟨w, hw, hrw, hwR⟩ := matrix_radius_annulus_eigenvalue hn A r R hr hR
  obtain ⟨z, hz, hdist⟩ := hcover w hrw hwR
  obtain ⟨v, hv, he⟩ := matrix_exists_unit_eigenvector A w hw
  refine ⟨z, hz, v, hv, ?_⟩
  rw [matrix_eigenvector_residual A w z v hv he]
  exact pow_le_pow_left₀ (norm_nonneg _) hdist.le 2

/-- The covering set is fixed before the dimension tends to infinity. -/
lemma exists_fixed_annulus_witness (r R δ : ℝ) (hδ : 0 < δ) :
    ∃ S : Finset ℂ, (∀ z ∈ S, r ≤ ‖z‖ ∧ ‖z‖ ≤ R) ∧
      ∀ n : ℕ, 0 < n → ∀ A : Matrix (Fin n) (Fin n) ℂ,
        r ≤ (spectralRadius ℂ A).toReal → ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ ≤ R →
        ∃ z ∈ S, ∃ v : EuclideanSpace ℂ (Fin n), ‖v‖ = 1 ∧
          ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A-z • 1) v‖^2 ≤ δ^2 := by
  obtain ⟨S, hS, hcover⟩ := complex_annulus_finite_cover r R δ hδ
  exact ⟨S, hS, matrix_annulus_approximate_vector r R δ S hcover⟩

lemma complex_annulus_bulk_subset (r R δ u : ℝ) (S : Finset ℂ)
    (hcover : ∀ w : ℂ, r ≤ ‖w‖ → ‖w‖ ≤ R → ∃ z ∈ S, ‖w-z‖ < δ)
    (L : ℂ → ℝ) (n : ℕ) (hn : 0 < n) :
    {x : Fin n → Fin n → ℂ | r ≤ (spectralRadius ℂ (normalizedArray x)).toReal ∧
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (normalizedArray x)‖ ≤ R ∧
      ∀ z ∈ S, regularizedResidualLogDet x z (2*u)/(n : ℝ) ≤ L z} ⊆
        ⋃ z ∈ S, complexApproximateBulkEvent n u z (δ^2) (L z) := by
  intro x hx
  obtain ⟨z, hz, v, hv, hd⟩ := matrix_annulus_approximate_vector r R δ S hcover n hn
    (normalizedArray x) hx.1 hx.2.1
  exact Set.mem_iUnion.mpr ⟨z, Set.mem_iUnion.mpr ⟨hz, ⟨⟨v, hv, hd⟩, hx.2.2 z hz⟩⟩⟩

#print axioms matrix_annulus_approximate_vector
#print axioms exists_fixed_annulus_witness
#print axioms complex_annulus_bulk_subset
end SpectralRadiusUpperTail
