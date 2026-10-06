import SpectralRadiusUpperTail.MarkedRealChartBranchOpen
import SpectralRadiusUpperTail.MarkedRealRootRegularFrame
import Mathlib.Topology.Bases
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open Set
open scoped Matrix

/-- Every simple-spectrum real eigenvalue mark lies in an open local
Schur branch where that mark is the chart's scalar coordinate. -/
theorem markedReal_simpleRoot_mem_chartBranch
    (m : ℕ) (hm : 0 < m)
    (A : Matrix (RealSchurMixedCoord (markedRealTwoBlockSizes m))
      (RealSchurMixedCoord (markedRealTwoBlockSizes m)) ℝ)
    (hsep : A.charpoly.Separable)
    (x : ℝ) (hx : A.charpoly.IsRoot x) :
    (A,x) ∈ ⋃ c : RealSchurMixedRegularFrame (markedRealTwoBlockSizes m),
      markedRealChartBranch m c := by
  obtain ⟨c,hxcoord,hA⟩ :=
    exists_markedRealRoot_regular_frame m hm A hsep x hx
  have hsepT : c.T.charpoly.Separable := by
    rw [hA, realMatrixOrthogonalConjugation_charpoly _ c.Q c.T c.orthogonal] at hsep
    exact hsep
  have hc := markedRealChartBranch_center_mem m hm c hsepT
  rw [hxcoord] at hc
  rw [hA]
  exact mem_iUnion_of_mem c hc

/-- A single countable family of open marked-root branches covers all
simple-spectrum real roots. The countable selection is made in the
matrix-root product, so distinct roots of one matrix are retained. -/
theorem exists_countable_markedRealChartBranch_cover
    (m : ℕ) (hm : 0 < m) :
    ∃ C : Set (RealSchurMixedRegularFrame (markedRealTwoBlockSizes m)),
      C.Countable ∧
      ∀ (A : Matrix (RealSchurMixedCoord (markedRealTwoBlockSizes m))
        (RealSchurMixedCoord (markedRealTwoBlockSizes m)) ℝ)
        (x : ℝ), A.charpoly.Separable → A.charpoly.IsRoot x →
          ∃ c ∈ C, (A,x) ∈ markedRealChartBranch m c := by
  let : SecondCountableTopology
      (Matrix (RealSchurMixedCoord (markedRealTwoBlockSizes m))
        (RealSchurMixedCoord (markedRealTwoBlockSizes m)) ℝ × ℝ) :=
    inferInstanceAs
      (SecondCountableTopology
        ((RealSchurMixedCoord (markedRealTwoBlockSizes m) →
          RealSchurMixedCoord (markedRealTwoBlockSizes m) → ℝ) × ℝ))
  obtain ⟨C,hC,hcover⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun c : RealSchurMixedRegularFrame (markedRealTwoBlockSizes m) =>
      markedRealChartBranch m c)
    (isOpen_markedRealChartBranch m)
  refine ⟨C,hC,?_⟩
  intro A x hsep hx
  have hmem := markedReal_simpleRoot_mem_chartBranch m hm A hsep x hx
  rw [← hcover] at hmem
  simpa only [mem_iUnion, exists_prop] using hmem

#print axioms markedReal_simpleRoot_mem_chartBranch
#print axioms exists_countable_markedRealChartBranch_cover
end SpectralRadiusUpperTail
