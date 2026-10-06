import SpectralRadiusUpperTail.RealSchurFixedRegularLocus
import Mathlib.Topology.Bases
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- A mixed-Schur chart viewed in a fixed `Fin n` matrix space. -/
structure RealSchurFixedChartIndex (n : ℕ) where
  shape : List ℕ
  small : ∀ k ∈ shape, k = 1 ∨ k = 2
  positive : ∀ i, 0 < realSchurListBlockSize shape i
  indexEquiv : Fin n ≃ RealSchurMixedCoord (realSchurListBlockSize shape)
  frame : RealSchurMixedRegularFrame (realSchurListBlockSize shape)

def RealSchurFixedChartIndex.target {n : ℕ}
    (c : RealSchurFixedChartIndex n) :
    Set (Matrix (Fin n) (Fin n) ℝ) :=
  (Matrix.reindex c.indexEquiv c.indexEquiv) ⁻¹' c.frame.chart.target

theorem RealSchurFixedChartIndex.isOpen_target {n : ℕ}
    (c : RealSchurFixedChartIndex n) : IsOpen c.target := by
  have hcont : Continuous
      (Matrix.reindex c.indexEquiv c.indexEquiv :
        Matrix (Fin n) (Fin n) ℝ →
          Matrix (RealSchurMixedCoord (realSchurListBlockSize c.shape))
            (RealSchurMixedCoord (realSchurListBlockSize c.shape)) ℝ) := by
    have h := (Matrix.reindexLinearEquiv ℝ ℝ
      c.indexEquiv c.indexEquiv).continuous_of_finiteDimensional
    change Continuous (Matrix.reindex c.indexEquiv c.indexEquiv :
      Matrix (Fin n) (Fin n) ℝ →
        Matrix (RealSchurMixedCoord (realSchurListBlockSize c.shape))
          (RealSchurMixedCoord (realSchurListBlockSize c.shape)) ℝ) at h
    exact h
  exact c.frame.chart.open_target.preimage hcont

theorem iUnion_realSchurFixedChartIndex_target (n : ℕ) :
    (⋃ c : RealSchurFixedChartIndex n, c.target) =
      realSchurFixedRegularLocus n := by
  ext A
  constructor
  · intro h
    obtain ⟨c,hc⟩ := Set.mem_iUnion.mp h
    exact (realSchurFixedRegularLocus_mem_iff A).mpr
      ⟨c.shape, c.small, c.indexEquiv,
        Set.mem_iUnion_of_mem c.frame hc⟩
  · intro h
    obtain ⟨s,hs,e,he⟩ := (realSchurFixedRegularLocus_mem_iff A).mp h
    obtain ⟨c,hc⟩ := Set.mem_iUnion.mp he
    exact Set.mem_iUnion_of_mem
      ⟨s,hs,realSchurListBlockSize_pos s hs,e,c⟩ hc

/-- A single countable family of fixed-coordinate open charts covers
the full-measure regular locus. -/
theorem exists_countable_realSchurFixedRegularAtlas (n : ℕ) :
    ∃ C : Set (RealSchurFixedChartIndex n), C.Countable ∧
      (⋃ c ∈ C, c.target) = realSchurFixedRegularLocus n := by
  let : SecondCountableTopology (Matrix (Fin n) (Fin n) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℝ))
  obtain ⟨C,hC,hcover⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun c : RealSchurFixedChartIndex n => c.target)
    (fun c => c.isOpen_target)
  exact ⟨C,hC,by rw [hcover, iUnion_realSchurFixedChartIndex_target]⟩

#print axioms exists_countable_realSchurFixedRegularAtlas
end SpectralRadiusUpperTail
