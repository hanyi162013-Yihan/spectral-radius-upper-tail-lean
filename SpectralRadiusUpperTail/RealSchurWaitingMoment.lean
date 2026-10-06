import SpectralRadiusUpperTail.RealSchurPathMoment
import SpectralRadiusUpperTail.SchurWaitingSum

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators Matrix.Norms.Frobenius

/-- All allocations of the diagonal steps along a fixed mixed real Schur path.
The allocations use the same random blocks, so they need not be independent. -/
noncomputable def realSchurWaitingSum (n k l : ℕ)
    (B : Fin (l+1) → RealSchurBlockData)
    (z : (Fin (l+1) → ℝ) × GaussianBridgeSpace 2 l) : Matrix (Fin 2) (Fin 2) ℝ :=
  ∑ m : SchurWaitingTimes k l, realSchurPathProduct n l B m.val z

theorem real_schur_waiting_second_moment (n k l : ℕ) (hn : 0 < n) (hlk : l ≤ k)
    (η ρ : ℝ) (hη : 0 < η) (B : Fin (l+1) → RealSchurBlockData)
    (hB : ∀ i, realSchurDataAdmissible (B i))
    (hmod : ∀ i, realSchurDataRadius (B i) ≤ ρ) :
    Integrable (fun z => ‖realSchurWaitingSum n k l B z‖^2) (realSchurPathLaw n l B) ∧
    (∫ z, ‖realSchurWaitingSum n k l B z‖^2 ∂realSchurPathLaw n l B) ≤
      (k.choose l : ℝ)^2 * ((1/(n : ℝ))^l *
        (2+2/((n : ℝ)*η^2))^(l+1)*(ρ+η)^(2*(k-l))) := by
  apply schur_waiting_sum_second_moment (realSchurPathLaw n l B) k l hlk
    (fun m z => realSchurPathProduct n l B m.val z)
  · exact fun m a b => realSchurPathProduct_entry_measurable n l B hB m.val a b
  · exact fun m => (real_schur_path_second_moment n l hn η ρ hη B hB m.val hmod).1
  · intro m
    simpa only [m.property] using
      (real_schur_path_second_moment n l hn η ρ hη B hB m.val hmod).2

#print axioms real_schur_waiting_second_moment
end SpectralRadiusUpperTail
