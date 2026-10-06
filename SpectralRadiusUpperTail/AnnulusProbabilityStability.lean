import SpectralRadiusUpperTail.FiniteRightDeformationProbability
import SpectralRadiusUpperTail.ResolventProbabilityStability

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology Matrix Matrix.Norms.L2Operator

lemma annulus_probability_stability (Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)]
    (μ : (n : ℕ) → Measure (Ω n)) [∀ n, IsFiniteMeasure (μ n)]
    (A E : (n : ℕ) → Ω n → Matrix (Fin n) (Fin n) ℂ)
    (r L B : ℝ) (hB : 0 < B)
    (hbase : Tendsto (fun n => (μ n).real {x | ¬ matrixAnnulusControl (A n x) r L B})
      atTop (𝓝 0))
    (herr : ∀ ε : ℝ, 0 < ε → Tendsto (fun n => (μ n).real
      {x | ε ≤ ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (E n x)‖}) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => (μ n).real {x | ¬ ∀ z : ℂ, r ≤ ‖z‖ → ‖z‖ ≤ L →
      z ∈ resolventSet ℂ (A n x+E n x) ∧
      ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (resolvent (A n x+E n x) z)‖ ≤ 2*B ∧
      ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)
        (resolvent (A n x+E n x) z-resolvent (A n x) z)‖ < ε}) atTop (𝓝 0) := by
  have hb : Tendsto (fun n => (μ n).real {x | ¬ ∀ z ∈ {z : ℂ | r ≤ ‖z‖ ∧ ‖z‖ ≤ L},
      z ∈ resolventSet ℂ (A n x) ∧ ‖resolvent (A n x) z‖ ≤ B}) atTop (𝓝 0) := by
    simpa only [Set.mem_setOf_eq,and_imp,matrixAnnulusControl,Matrix.l2_opNorm_toEuclideanCLM] using hbase
  have hh := resolvent_probability_stability Ω (fun n => Matrix (Fin n) (Fin n) ℂ)
    μ A E {z : ℂ | r ≤ ‖z‖ ∧ ‖z‖ ≤ L} B hB hb herr ε hε
  simpa only [Set.mem_setOf_eq,and_imp,Matrix.l2_opNorm_toEuclideanCLM] using hh

#print axioms annulus_probability_stability
end SpectralRadiusUpperTail
