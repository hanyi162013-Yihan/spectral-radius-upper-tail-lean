import SpectralRadiusUpperTail.RealSchurMixedRegularAtlas
import Mathlib.Topology.Bases
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

instance realSchurMixedMatrixMeasurableSpace
    {m : ℕ} (s : Fin m → ℕ) :
    MeasurableSpace
      (Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ) :=
  borel (Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)

instance realSchurMixedMatrixBorelSpace
    {m : ℕ} (s : Fin m → ℕ) :
    BorelSpace
      (Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ) := ⟨rfl⟩

/-- A countable regular atlas can be enumerated whenever the specified
block shape has at least one regular frame. -/
theorem exists_realSchurMixedRegularAtlasSequence
    {m : ℕ} (s : Fin m → ℕ) (c₀ : RealSchurMixedRegularFrame s) :
    ∃ c : ℕ → RealSchurMixedRegularFrame s,
      ∀ (T Q : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ),
        realSchurMixedLowerProjection s T = 0 →
        (realSchurMixedOrbitMatrix s T).det ≠ 0 →
        Qᵀ*Q=1 →
        ∃ k, Q*T*Qᵀ ∈ (c k).chart.target := by
  classical
  obtain ⟨C,hC,hcover⟩ := exists_countable_realSchurMixedRegularAtlas s
  have hne : C.Nonempty := by
    obtain ⟨c,hc,_⟩ := hcover c₀.T c₀.Q c₀.upper c₀.regular c₀.orthogonal
    exact ⟨c,hc⟩
  obtain ⟨c,hc⟩ := hC.exists_eq_range hne
  refine ⟨c, ?_⟩
  intro T Q hT hdet hQ
  obtain ⟨d,hd,hm⟩ := hcover T Q hT hdet hQ
  have hr : d ∈ Set.range c := by simpa only [hc] using hd
  obtain ⟨k,hk⟩ := hr
  exact ⟨k, hk ▸ hm⟩

/-- The first-index patch removes all earlier chart targets. -/
def realSchurMixedRegularFirstPatch
    {m : ℕ} {s : Fin m → ℕ}
    (c : ℕ → RealSchurMixedRegularFrame s) (k : ℕ) :
    Set (Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ) :=
  (c k).chart.target \ ⋃ j ∈ Finset.range k, (c j).chart.target

theorem measurableSet_realSchurMixedRegularFirstPatch
    {m : ℕ} {s : Fin m → ℕ}
    (c : ℕ → RealSchurMixedRegularFrame s) (k : ℕ) :
    MeasurableSet (realSchurMixedRegularFirstPatch c k) := by
  exact (c k).chart.open_target.measurableSet.diff
    (Finset.measurableSet_biUnion _ fun j _ =>
      (c j).chart.open_target.measurableSet)

/-- First-index patch targets are genuinely disjoint, independent of
the amount of overlap among the original inverse-function charts. -/
theorem pairwise_realSchurMixedRegularFirstPatch
    {m : ℕ} {s : Fin m → ℕ}
    (c : ℕ → RealSchurMixedRegularFrame s) :
    Pairwise (fun i j => Disjoint
      (realSchurMixedRegularFirstPatch c i)
      (realSchurMixedRegularFirstPatch c j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro A hi hj
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact hj.2 (Set.mem_iUnion_of_mem i
      (Set.mem_iUnion_of_mem (Finset.mem_range.mpr hij) hi.1))
  · exact hi.2 (Set.mem_iUnion_of_mem j
      (Set.mem_iUnion_of_mem (Finset.mem_range.mpr hji) hj.1))

/-- The disjointification retains precisely the union of chart targets. -/
theorem iUnion_realSchurMixedRegularFirstPatch
    {m : ℕ} {s : Fin m → ℕ}
    (c : ℕ → RealSchurMixedRegularFrame s) :
    (⋃ k, realSchurMixedRegularFirstPatch c k) =
      ⋃ k, (c k).chart.target := by
  classical
  apply Set.ext
  intro A
  constructor
  · intro h
    obtain ⟨k,hk⟩ := Set.mem_iUnion.mp h
    exact Set.mem_iUnion_of_mem k hk.1
  · intro h
    have hp : ∃ k, A ∈ (c k).chart.target := Set.mem_iUnion.mp h
    let k := Nat.find hp
    refine Set.mem_iUnion_of_mem k ⟨Nat.find_spec hp, ?_⟩
    intro hearly
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hearly
    obtain ⟨hjk,hAj⟩ := Set.mem_iUnion.mp hj
    exact Nat.find_min hp (Finset.mem_range.mp hjk) hAj

#print axioms exists_realSchurMixedRegularAtlasSequence
#print axioms iUnion_realSchurMixedRegularFirstPatch
end SpectralRadiusUpperTail
