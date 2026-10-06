import SpectralRadiusUpperTail.RealSchurFiniteMultiplicity
import SpectralRadiusUpperTail.RealGaussianActualSimpleSpectrum

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix Matrix.Norms.Operator BigOperators

/-- Exact finite-cover normalization for the actual iid real Gaussian
matrix law. Every shape, index reordering, and code is included, while
the reciprocal total multiplicity counts each sampled matrix only once. -/
theorem realGaussian_lintegral_finiteCode_normalized
    (n : ℕ) (g : ((Fin n × Fin n) → ℝ) → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ x, g x ∂gaussianMatrixLaw n) =
      ∑ I : RealSchurFiniteCode n,
        ∫⁻ x in {x | Matrix.of x.curry ∈ realSchurFiniteCodeClass I},
          (realSchurFiniteMultiplicity n (Matrix.of x.curry))⁻¹*g x ∂gaussianMatrixLaw n := by
  classical
  let S := fun I : RealSchurFiniteCode n =>
    {x : (Fin n × Fin n) → ℝ | Matrix.of x.curry ∈ realSchurFiniteCodeClass I}
  have hC : Continuous (fun x : (Fin n × Fin n) → ℝ => Matrix.of x.curry) := by
    apply continuous_matrix
    intro i j
    exact continuous_apply (i,j)
  have hS : ∀ I, MeasurableSet (S I) := fun I =>
    (measurableSet_realSchurFiniteCodeClass I).preimage hC.measurable
  have hM (x : (Fin n × Fin n) → ℝ) :
      finiteCoverMultiplicity S x=realSchurFiniteMultiplicity n (Matrix.of x.curry) := rfl
  have h := lintegral_finiteCover_normalized S hS (gaussianMatrixLaw n) g hg
  have hfull : ∀ᵐ x ∂gaussianMatrixLaw n, x ∈ ⋃ I, S I := by
    filter_upwards [realGaussianMatrix_charpoly_separable_ae n] with x hx
    obtain ⟨I,hI⟩ := Set.mem_iUnion.mp (realMatrix_mem_finiteSchurCodeUnion (Matrix.of x.curry) hx)
    exact Set.mem_iUnion_of_mem I hI
  rw [Measure.restrict_eq_self_of_ae_mem hfull] at h
  simpa only [hM] using h.symm

#print axioms realGaussian_lintegral_finiteCode_normalized
end SpectralRadiusUpperTail
