import SpectralRadiusUpperTail.RealSchurFixedMatrixChartCoverage
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Matrix

/-- The union of all regular mixed-Schur chart loci in the fixed
`Fin n` matrix coordinate space, allowing finite reindexing. -/
def realSchurFixedRegularLocus (n : ℕ) :
    Set (Matrix (Fin n) (Fin n) ℝ) :=
  ⋃ s : List ℕ,
    ⋃ _ : ∀ k ∈ s, k = 1 ∨ k = 2,
      ⋃ e : Fin n ≃ RealSchurMixedCoord (realSchurListBlockSize s),
        (Matrix.reindex e e) ⁻¹'
          realSchurMixedRegularChartLocus (realSchurListBlockSize s)

theorem realSchurFixedRegularLocus_mem_iff
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    A ∈ realSchurFixedRegularLocus n ↔
      ∃ s : List ℕ,
        (∀ k ∈ s, k = 1 ∨ k = 2) ∧
        ∃ e : Fin n ≃ RealSchurMixedCoord (realSchurListBlockSize s),
          Matrix.reindex e e A ∈
            realSchurMixedRegularChartLocus (realSchurListBlockSize s) := by
  simp only [realSchurFixedRegularLocus, Set.mem_iUnion, Set.mem_preimage,
    exists_prop]

theorem isOpen_realSchurFixedRegularLocus (n : ℕ) :
    IsOpen (realSchurFixedRegularLocus n) := by
  unfold realSchurFixedRegularLocus
  apply isOpen_iUnion
  intro s
  apply isOpen_iUnion
  intro hs
  apply isOpen_iUnion
  intro e
  have hcont : Continuous
      (Matrix.reindex e e : Matrix (Fin n) (Fin n) ℝ →
        Matrix (RealSchurMixedCoord (realSchurListBlockSize s))
          (RealSchurMixedCoord (realSchurListBlockSize s)) ℝ) := by
    have h := (Matrix.reindexLinearEquiv ℝ ℝ e e).continuous_of_finiteDimensional
    change Continuous (Matrix.reindex e e : Matrix (Fin n) (Fin n) ℝ →
      Matrix (RealSchurMixedCoord (realSchurListBlockSize s))
        (RealSchurMixedCoord (realSchurListBlockSize s)) ℝ) at h
    exact h
  exact (isOpen_realSchurMixedRegularChartLocus
    (realSchurListBlockSize s)).preimage hcont

theorem realSchurFixedRegularLocus_ae_gaussian (n : ℕ) :
    ∀ᵐ x : (Fin n × Fin n) → ℝ ∂gaussianMatrixLaw n,
      Matrix.of x.curry ∈ realSchurFixedRegularLocus n := by
  filter_upwards [realGaussianMatrix_exists_reindexed_regular_chart_ae n]
    with x hx
  obtain ⟨s, hs, e, he⟩ := hx
  exact (realSchurFixedRegularLocus_mem_iff _).mpr
    ⟨s, hs, e, he⟩

#print axioms realSchurFixedRegularLocus_ae_gaussian
end SpectralRadiusUpperTail
