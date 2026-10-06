import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open Metric Set

lemma complex_annulus_finite_cover (r R δ : ℝ) (hδ : 0 < δ) :
    ∃ S : Finset ℂ, (∀ z ∈ S, r ≤ ‖z‖ ∧ ‖z‖ ≤ R) ∧
      ∀ w : ℂ, r ≤ ‖w‖ → ‖w‖ ≤ R → ∃ z ∈ S, ‖w-z‖ < δ := by
  classical
  let K := {z : ℂ | r ≤ ‖z‖ ∧ ‖z‖ ≤ R}
  have hK : IsCompact K := by
    have hc := (isCompact_closedBall (0 : ℂ) R).inter_right
      (isClosed_le continuous_const continuous_norm : IsClosed {z : ℂ | r ≤ ‖z‖})
    convert! hc using 1
    ext z
    simp [K, Metric.mem_closedBall, dist_zero_right, and_comm]
  obtain ⟨T, hTK, hTf, hcover⟩ := hK.finite_cover_balls hδ
  refine ⟨hTf.toFinset, ?_, ?_⟩
  · intro z hz
    exact hTK (by simpa using hz)
  · intro w hrw hwR
    have hw := hcover (show w ∈ K from ⟨hrw, hwR⟩)
    obtain ⟨z, hz⟩ := Set.mem_iUnion.mp hw
    obtain ⟨hzT, hball⟩ := Set.mem_iUnion.mp hz
    exact ⟨z, by simpa using hzT, by simpa only [Metric.mem_ball, dist_eq_norm] using hball⟩

#print axioms complex_annulus_finite_cover
end SpectralRadiusUpperTail
