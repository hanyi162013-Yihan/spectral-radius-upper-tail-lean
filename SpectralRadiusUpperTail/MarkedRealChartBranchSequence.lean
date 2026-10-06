import SpectralRadiusUpperTail.MarkedRealChartBranchFiber
import SpectralRadiusUpperTail.RealSchurMixedSimpleSpectrum
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open Set
open scoped Matrix BigOperators

/-- A fixed countable sequence of marked-root branches covers every
simple-spectrum real root. Its indexing is chosen before the matrix. -/
theorem exists_markedRealChartBranch_sequence
    (m : ℕ) (hm : 0 < m) :
    ∃ c : ℕ → RealSchurMixedRegularFrame (markedRealTwoBlockSizes m),
      ∀ (A : Matrix (RealSchurMixedCoord (markedRealTwoBlockSizes m))
        (RealSchurMixedCoord (markedRealTwoBlockSizes m)) ℝ)
        (x : ℝ), A.charpoly.Separable → A.charpoly.IsRoot x →
          ∃ k, (A,x) ∈ markedRealChartBranch m (c k) := by
  classical
  obtain ⟨C,hC,hcover⟩ := exists_countable_markedRealChartBranch_cover m hm
  have hne : C.Nonempty := by
    obtain ⟨d,hd⟩ := finiteRealMatrix_diagonal_distinct_charpoly_separable
      (RealSchurMixedCoord (markedRealTwoBlockSizes m))
    let A := Matrix.diagonal d
    let i₀ := markedRealFirstCoordinate m
    have hx : A.charpoly.IsRoot (d i₀) := by
      rw [Matrix.charpoly_diagonal, Polynomial.IsRoot, Polynomial.eval_prod]
      apply Finset.prod_eq_zero (Finset.mem_univ i₀)
      simp
    obtain ⟨c,hc,_⟩ := hcover A (d i₀) hd hx
    exact ⟨c,hc⟩
  obtain ⟨c,hc⟩ := hC.exists_eq_range hne
  refine ⟨c, ?_⟩
  intro A x hsep hx
  obtain ⟨d,hd,hmemb⟩ := hcover A x hsep hx
  have hr : d ∈ Set.range c := by simpa only [hc] using hd
  obtain ⟨k,hk⟩ := hr
  exact ⟨k,hk ▸ hmemb⟩

#print axioms exists_markedRealChartBranch_sequence
end SpectralRadiusUpperTail
