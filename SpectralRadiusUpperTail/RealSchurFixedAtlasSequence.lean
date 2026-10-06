import SpectralRadiusUpperTail.RealSchurFixedCountableAtlas
import SpectralRadiusUpperTail.RealSchurMixedSimpleSpectrum
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Matrix

instance realSchurFixedMatrixMeasurableSpace (n : ℕ) :
    MeasurableSpace (Matrix (Fin n) (Fin n) ℝ) :=
  borel (Matrix (Fin n) (Fin n) ℝ)

instance realSchurFixedMatrixBorelSpace (n : ℕ) :
    BorelSpace (Matrix (Fin n) (Fin n) ℝ) := ⟨rfl⟩

theorem exists_realSchurFixedChartIndex (n : ℕ) :
    Nonempty (RealSchurFixedChartIndex n) := by
  obtain ⟨d,hd⟩ :=
    finiteRealMatrix_diagonal_distinct_charpoly_separable (Fin n)
  obtain ⟨s,hs,e,c,_⟩ :=
    realMatrix_exists_reindexed_regular_frame_of_separable
      (Matrix.diagonal d) hd
  exact ⟨⟨s,hs,realSchurListBlockSize_pos s hs,e,c⟩⟩

/-- A fixed sequence of open real-Schur charts covers the entire
regular locus of `Fin n` matrices. -/
theorem exists_realSchurFixedRegularAtlasSequence (n : ℕ) :
    ∃ c : ℕ → RealSchurFixedChartIndex n,
      (⋃ k, (c k).target) = realSchurFixedRegularLocus n := by
  classical
  obtain ⟨C,hC,hcover⟩ := exists_countable_realSchurFixedRegularAtlas n
  have hne : C.Nonempty := by
    obtain ⟨c₀⟩ := exists_realSchurFixedChartIndex n
    have hmem : c₀.frame.Q*c₀.frame.T*(c₀.frame.Q)ᵀ ∈
        c₀.frame.chart.target := c₀.frame.center_mem_target
    have hx : ∃ A : Matrix (Fin n) (Fin n) ℝ, A ∈ c₀.target := by
      refine ⟨Matrix.reindex c₀.indexEquiv.symm c₀.indexEquiv.symm
        (c₀.frame.Q*c₀.frame.T*(c₀.frame.Q)ᵀ), ?_⟩
      change Matrix.reindex c₀.indexEquiv c₀.indexEquiv
        (Matrix.reindex c₀.indexEquiv.symm c₀.indexEquiv.symm
          (c₀.frame.Q*c₀.frame.T*(c₀.frame.Q)ᵀ)) ∈
            c₀.frame.chart.target
      simpa using hmem
    obtain ⟨A,hA⟩ := hx
    have hLocus : A ∈ realSchurFixedRegularLocus n := by
      rw [← iUnion_realSchurFixedChartIndex_target n]
      exact Set.mem_iUnion_of_mem c₀ hA
    rw [← hcover] at hLocus
    obtain ⟨c,hc⟩ := Set.mem_iUnion.mp hLocus
    obtain ⟨hC,_⟩ := Set.mem_iUnion.mp hc
    exact ⟨c,hC⟩
  obtain ⟨c,hc⟩ := hC.exists_eq_range hne
  refine ⟨c, ?_⟩
  rw [← hcover, hc]
  ext A
  constructor
  · intro h
    obtain ⟨k,hk⟩ := Set.mem_iUnion.mp h
    exact Set.mem_iUnion_of_mem (c k)
      (Set.mem_iUnion_of_mem ⟨k,rfl⟩ hk)
  · intro h
    obtain ⟨d,hd⟩ := Set.mem_iUnion.mp h
    obtain ⟨hmem,hA⟩ := Set.mem_iUnion.mp hd
    obtain ⟨k,hk⟩ := hmem
    exact Set.mem_iUnion_of_mem k (hk ▸ hA)

/-- Disjointify a fixed countable atlas by assigning each matrix to
its first chart. -/
def realSchurFixedFirstPatch {n : ℕ}
    (c : ℕ → RealSchurFixedChartIndex n) (k : ℕ) :
    Set (Matrix (Fin n) (Fin n) ℝ) :=
  (c k).target \ ⋃ j ∈ Finset.range k, (c j).target

theorem measurableSet_realSchurFixedFirstPatch {n : ℕ}
    (c : ℕ → RealSchurFixedChartIndex n) (k : ℕ) :
    MeasurableSet (realSchurFixedFirstPatch c k) := by
  exact (c k).isOpen_target.measurableSet.diff
    (Finset.measurableSet_biUnion _ fun j _ =>
      (c j).isOpen_target.measurableSet)

theorem pairwise_realSchurFixedFirstPatch {n : ℕ}
    (c : ℕ → RealSchurFixedChartIndex n) :
    Pairwise (fun i j => Disjoint
      (realSchurFixedFirstPatch c i)
      (realSchurFixedFirstPatch c j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro A hi hj
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact hj.2 (Set.mem_iUnion_of_mem i
      (Set.mem_iUnion_of_mem (Finset.mem_range.mpr hij) hi.1))
  · exact hi.2 (Set.mem_iUnion_of_mem j
      (Set.mem_iUnion_of_mem (Finset.mem_range.mpr hji) hj.1))

theorem iUnion_realSchurFixedFirstPatch {n : ℕ}
    (c : ℕ → RealSchurFixedChartIndex n) :
    (⋃ k, realSchurFixedFirstPatch c k) =
      ⋃ k, (c k).target := by
  classical
  apply Set.ext
  intro A
  constructor
  · intro h
    obtain ⟨k,hk⟩ := Set.mem_iUnion.mp h
    exact Set.mem_iUnion_of_mem k hk.1
  · intro h
    have hp : ∃ k, A ∈ (c k).target := Set.mem_iUnion.mp h
    let k := Nat.find hp
    refine Set.mem_iUnion_of_mem k ⟨Nat.find_spec hp, ?_⟩
    intro hearly
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hearly
    obtain ⟨hjk,hAj⟩ := Set.mem_iUnion.mp hj
    exact Nat.find_min hp (Finset.mem_range.mp hjk) hAj

#print axioms exists_realSchurFixedRegularAtlasSequence
#print axioms iUnion_realSchurFixedFirstPatch
end SpectralRadiusUpperTail
