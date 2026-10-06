import SpectralRadiusUpperTail.UniformPowerResolvent
import SpectralRadiusUpperTail.MatrixOperatorComparison

namespace SpectralRadiusUpperTail
open scoped BigOperators Matrix.Norms.L2Operator

/-- Exterior control uses the Euclidean operator norm explicitly. -/
def matrixExteriorControl {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (r C : ℝ) : Prop :=
  ∀ z : ℂ, r ≤ ‖z‖ → z ∈ resolventSet ℂ A ∧
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (resolvent A z)‖ ≤ C

lemma matrixExteriorControl_of_power {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℂ) (r M : ℝ) (hr : 0 < r) (m : ℕ)
    (hA : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A‖ ≤ M)
    (hp : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (A^m)‖ ≤ r^m/2) :
    matrixExteriorControl A r (max 1 ((2*∑ j ∈ Finset.range m, (M/r)^j)/r)) := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have hh := uniform_resolvent_of_power_bound (𝕂 := ℂ) A r M hr hA m hp
  intro z hz
  exact ⟨(hh z hz).1,(hh z hz).2.trans (le_max_right _ _)⟩

#print axioms matrixExteriorControl
#print axioms matrixExteriorControl_of_power
end SpectralRadiusUpperTail
