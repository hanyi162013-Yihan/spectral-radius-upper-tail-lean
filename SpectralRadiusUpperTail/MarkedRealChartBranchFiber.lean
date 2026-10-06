import SpectralRadiusUpperTail.MarkedRealChartBranchCoverage
import SpectralRadiusUpperTail.CountableChartFiberCount
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open Set

private abbrev MarkedMatrix (m : ℕ) :=
  Matrix (RealSchurMixedCoord (markedRealTwoBlockSizes m))
    (RealSchurMixedCoord (markedRealTwoBlockSizes m)) ℝ

/-- The simple-spectrum real-root incidence space in the mixed Schur
matrix coordinates. The cutoff is part of the marked space. -/
abbrev MarkedRealSimpleRootIncidence (m : ℕ) (b : ℝ) :=
  {p : MarkedMatrix m × ℝ //
    p.1.charpoly.Separable ∧ p.1.charpoly.IsRoot p.2 ∧ b < p.2}

abbrev markedRealSimpleRootProjection (m : ℕ) (b : ℝ) :
    MarkedRealSimpleRootIncidence m b → MarkedMatrix m :=
  fun p => p.val.1

def markedRealIncidenceChartBranch (m : ℕ) (b : ℝ)
    (c : RealSchurMixedRegularFrame (markedRealTwoBlockSizes m)) :
    Set (MarkedRealSimpleRootIncidence m b) :=
  {p | p.val ∈ markedRealChartBranch m c}

/-- One local marked-root branch projects injectively to matrices:
the complementary spectral gap makes its scalar root unique. -/
theorem markedRealIncidenceChartBranch_projection_inj
    (m : ℕ) (hm : 0 < m) (b : ℝ)
    (c : RealSchurMixedRegularFrame (markedRealTwoBlockSizes m)) :
    InjOn (markedRealSimpleRootProjection m b)
      (markedRealIncidenceChartBranch m b c) := by
  intro p hp q hq heq
  apply Subtype.ext
  apply Prod.ext
  · exact heq
  · have hpx := markedRealChartBranch_root_eq_scalar
      m hm c p.val hp p.property.2.1
    have hqx := markedRealChartBranch_root_eq_scalar
      m hm c q.val hq q.property.2.1
    change p.val.1 = q.val.1 at heq
    rw [heq] at hpx
    exact hpx.trans hqx.symm

/-- The open branch family covers every marked simple real root, for
every cutoff. This is coverage in the incidence space, retaining all
distinct real roots of a matrix. -/
theorem iUnion_markedRealIncidenceChartBranch
    (m : ℕ) (hm : 0 < m) (b : ℝ) :
    (⋃ c : RealSchurMixedRegularFrame (markedRealTwoBlockSizes m),
      markedRealIncidenceChartBranch m b c) = Set.univ := by
  ext p
  simp only [mem_iUnion, mem_univ, iff_true]
  obtain ⟨c,hc⟩ := Set.mem_iUnion.mp
    (markedReal_simpleRoot_mem_chartBranch
      m hm p.val.1 p.property.1 p.val.2 p.property.2.1)
  exact ⟨c,hc⟩

#print axioms markedRealIncidenceChartBranch_projection_inj
#print axioms iUnion_markedRealIncidenceChartBranch
end SpectralRadiusUpperTail
