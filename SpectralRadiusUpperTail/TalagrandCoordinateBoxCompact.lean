import SpectralRadiusUpperTail.TalagrandHullGeometry
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open WithLp Set
variable {𝕂 : Type*} [RCLike 𝕂]

/-- A uniform coordinate box is compact in every finite Euclidean product. -/
lemma coordinateBox_compact (N : ℕ) (K : ℝ) :
    IsCompact (coordinateBox (𝕂 := 𝕂) N K) := by
  let C : Set (Fin N → 𝕂) :=
    Set.pi Set.univ (fun _ : Fin N => Metric.closedBall (0 : 𝕂) K)
  have hC : IsCompact C := isCompact_univ_pi (fun _ => isCompact_closedBall _ _)
  have hEq : coordinateBox (𝕂 := 𝕂) N K =
      (toLp 2 : (Fin N → 𝕂) → EuclideanSpace 𝕂 (Fin N)) '' C := by
    ext x
    constructor
    · intro hx
      refine ⟨fun i => x i, ?_, ?_⟩
      · intro i _
        simpa only [Metric.mem_closedBall, dist_zero_right] using hx i
      · ext i
        rfl
    · rintro ⟨y, hy, rfl⟩
      intro i
      simpa only [Metric.mem_closedBall, dist_zero_right] using hy i (Set.mem_univ i)
  rw [hEq]
  exact hC.image (PiLp.continuous_toLp 2 _)

#print axioms coordinateBox_compact
end SpectralRadiusUpperTail
