import SpectralRadiusUpperTail.RealSchurFixedPatchIntegration
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Matrix

/-- Assign each fixed matrix-entry array to the first regular chart in
the chosen countable sequence that contains it. -/
def realSchurFixedEntryFirstPatch {n : ℕ}
    (c : ℕ → RealSchurFixedChartIndex n) (k : ℕ) :
    Set ((Fin n × Fin n) → ℝ) :=
  (fun x => Matrix.of x.curry) ⁻¹' realSchurFixedFirstPatch c k

theorem measurableSet_realSchurFixedEntryFirstPatch {n : ℕ}
    (c : ℕ → RealSchurFixedChartIndex n) (k : ℕ) :
    MeasurableSet (realSchurFixedEntryFirstPatch c k) := by
  have hflat : Measurable
      (fun x : (Fin n × Fin n) → ℝ => Matrix.of x.curry) := by
    exact (realMatrixEntryEquiv (Fin n)).symm.continuous_of_finiteDimensional.measurable
  exact (measurableSet_realSchurFixedFirstPatch c k).preimage hflat

theorem pairwise_realSchurFixedEntryFirstPatch {n : ℕ}
    (c : ℕ → RealSchurFixedChartIndex n) :
    Pairwise (fun i j => Disjoint
      (realSchurFixedEntryFirstPatch c i)
      (realSchurFixedEntryFirstPatch c j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  exact Set.disjoint_left.mp (pairwise_realSchurFixedFirstPatch c hij)
    hxi hxj

theorem iUnion_realSchurFixedEntryFirstPatch {n : ℕ}
    (c : ℕ → RealSchurFixedChartIndex n) :
    (⋃ k, realSchurFixedEntryFirstPatch c k) =
      (fun x => Matrix.of x.curry) ⁻¹' (⋃ k, (c k).target) := by
  ext x
  have h := congrArg
    (fun S : Set (Matrix (Fin n) (Fin n) ℝ) => Matrix.of x.curry ∈ S)
    (iUnion_realSchurFixedFirstPatch c)
  simpa only [realSchurFixedEntryFirstPatch, Set.mem_iUnion,
    Set.mem_preimage] using (Iff.of_eq h)

#print axioms iUnion_realSchurFixedEntryFirstPatch
end SpectralRadiusUpperTail
