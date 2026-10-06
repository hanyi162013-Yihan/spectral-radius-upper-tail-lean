import SpectralRadiusUpperTail.RealSchurMixedRegularAtlas
import SpectralRadiusUpperTail.RealSchurMixedOrbitRegular
import Mathlib.Topology.Bases
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- The open locus reached by all regular local mixed-Schur charts of a
fixed block shape. This definition makes no claim that every real matrix
belongs to the locus. -/
def realSchurMixedRegularChartLocus
    {m : ℕ} (s : Fin m → ℕ) :
    Set (Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ) :=
  ⋃ c : RealSchurMixedRegularFrame s, c.chart.target

theorem isOpen_realSchurMixedRegularChartLocus
    {m : ℕ} (s : Fin m → ℕ) :
    IsOpen (realSchurMixedRegularChartLocus s) := by
  exact isOpen_iUnion (fun c : RealSchurMixedRegularFrame s => c.chart.open_target)

/-- Second countability selects a countable family covering the entire
regular chart locus, not merely the set of chart centers. -/
theorem exists_countable_realSchurMixedRegularChartLocus
    {m : ℕ} (s : Fin m → ℕ) :
    ∃ C : Set (RealSchurMixedRegularFrame s), C.Countable ∧
      (⋃ c ∈ C, c.chart.target) = realSchurMixedRegularChartLocus s := by
  let : SecondCountableTopology
      (Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ) :=
    inferInstanceAs
      (SecondCountableTopology (RealSchurMixedCoord s → RealSchurMixedCoord s → ℝ))
  obtain ⟨C,hC,hcover⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun c : RealSchurMixedRegularFrame s => c.chart.target)
    (fun c => c.chart.open_target)
  exact ⟨C,hC,by simpa only [realSchurMixedRegularChartLocus] using hcover⟩

theorem realSchurMixedRegularFrame_center_mem_locus
    {m : ℕ} {s : Fin m → ℕ} (c : RealSchurMixedRegularFrame s) :
    c.Q*c.T*c.Qᵀ ∈ realSchurMixedRegularChartLocus s :=
  Set.mem_iUnion_of_mem c c.center_mem_target

/-- Every separated admissible real-Schur representation is in the
regular chart locus. Thus a global decomposition theorem for simple
matrices would supply the missing almost-everywhere coverage. -/
theorem realSchurMixedChart_representation_mem_regular_locus
    {m : ℕ} (B : Fin m → RealSchurChartBlock)
    (T : Matrix (RealSchurMixedCoord (fun i => (B i).size))
      (RealSchurMixedCoord (fun i => (B i).size)) ℝ)
    (hT : ∀ a b : Fin m, b < a →
      ∀ x : Fin ((B a).size), ∀ y : Fin ((B b).size),
        T ⟨a,x⟩ ⟨b,y⟩ = 0)
    (hdiag : ∀ i a b, T ⟨i,a⟩ ⟨i,b⟩ = (B i).matrix a b)
    (hsep : ∀ p : RealSchurLowerIndex m,
      realSchurDataSeparated (B p.1.1).data (B p.1.2).data)
    (Q : Matrix (RealSchurMixedCoord (fun i => (B i).size))
      (RealSchurMixedCoord (fun i => (B i).size)) ℝ)
    (hQ : Qᵀ*Q=1) :
    Q*T*Qᵀ ∈ realSchurMixedRegularChartLocus (fun i => (B i).size) := by
  let s := fun i : Fin m => (B i).size
  have hupper : realSchurMixedLowerProjection s T = 0 := by
    apply (realSchurMixed_blockTriangular_iff_lower_zero s T).mp
    intro u v huv
    exact hT u.1 v.1 huv u.2 v.2
  let c : RealSchurMixedRegularFrame s :=
    ⟨T, hupper, realSchurChartBlock_orbit_det_ne_zero B T hT hdiag hsep,
      Q, hQ⟩
  exact realSchurMixedRegularFrame_center_mem_locus c

/-- When one regular frame exists, the complete open locus admits a
fixed sequence of local charts, selected before any matrix is sampled. -/
theorem exists_realSchurMixedRegularChartLocusSequence
    {m : ℕ} (s : Fin m → ℕ) (c₀ : RealSchurMixedRegularFrame s) :
    ∃ c : ℕ → RealSchurMixedRegularFrame s,
      (⋃ k, (c k).chart.target) = realSchurMixedRegularChartLocus s := by
  classical
  obtain ⟨C,hC,hcover⟩ := exists_countable_realSchurMixedRegularChartLocus s
  have hne : C.Nonempty := by
    have hmem := realSchurMixedRegularFrame_center_mem_locus c₀
    rw [← hcover] at hmem
    obtain ⟨c,hc⟩ := Set.mem_iUnion.mp hmem
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

#print axioms exists_realSchurMixedRegularChartLocusSequence
end SpectralRadiusUpperTail
