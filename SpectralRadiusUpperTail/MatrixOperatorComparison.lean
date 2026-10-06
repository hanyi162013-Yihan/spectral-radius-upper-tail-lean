import SpectralRadiusUpperTail.SecondMomentProbability
import Mathlib.Analysis.CStarAlgebra.Matrix

namespace SpectralRadiusUpperTail
open MeasureTheory Filter WithLp
open scoped BigOperators Matrix.Norms.Frobenius Topology

/-- Euclidean operator norm is bounded by the actual Frobenius norm. -/
lemma euclidean_operator_norm_le_frobenius {𝕂 : Type*} [RCLike 𝕂] {N : ℕ}
    (A : Matrix (Fin N) (Fin N) 𝕂) : ‖Matrix.toEuclideanCLM (n := Fin N) (𝕜 := 𝕂) A‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro x
  have he : A * Matrix.replicateCol (Fin 1) (ofLp x) =
      Matrix.replicateCol (Fin 1) (A.mulVec (ofLp x)) := by
    ext i j
    rfl
  have hh := Matrix.frobenius_norm_mul A (Matrix.replicateCol (Fin 1) (ofLp x))
  have hcol (y : Fin N → 𝕂) : ‖Matrix.replicateCol (Fin 1) y‖ = ‖toLp 2 y‖ := by
    convert! Matrix.frobenius_norm_replicateCol (ι := Fin 1) y using 1
  rw [he, hcol, hcol, ← Matrix.toEuclideanCLM_toLp] at hh
  simpa only [toLp_ofLp] using hh

lemma operator_probability_le_frobenius {Ω 𝕂 : Type*} [MeasurableSpace Ω] [RCLike 𝕂]
    {N : ℕ} (μ : Measure Ω) [IsFiniteMeasure μ] (A : Ω → Matrix (Fin N) (Fin N) 𝕂) (r : ℝ) :
    μ.real {x | r ≤ ‖Matrix.toEuclideanCLM (n := Fin N) (𝕜 := 𝕂) (A x)‖} ≤ μ.real {x | r ≤ ‖A x‖} := by
  exact measureReal_mono (μ := μ) (fun x hx => hx.trans (euclidean_operator_norm_le_frobenius (A x)))

/-- Norm comparison transfers a proved Frobenius probability limit to the
Euclidean operator norm, including varying matrix dimensions. -/
theorem operator_probability_tendsto_of_frobenius {𝕂 : Type*} [RCLike 𝕂]
    (Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)]
    (μ : (n : ℕ) → Measure (Ω n)) [∀ n, IsFiniteMeasure (μ n)] (N : ℕ → ℕ)
    (A : (n : ℕ) → Ω n → Matrix (Fin (N n)) (Fin (N n)) 𝕂) (r : ℝ)
    (hf : Tendsto (fun n => (μ n).real {x | r ≤ ‖A n x‖}) atTop (𝓝 0)) :
    Tendsto (fun n => (μ n).real {x | r ≤ ‖Matrix.toEuclideanCLM (n := Fin (N n)) (𝕜 := 𝕂) (A n x)‖}) atTop (𝓝 0) := by
  exact squeeze_zero (fun _ => measureReal_nonneg)
    (fun n => operator_probability_le_frobenius (μ n) (A n) r) hf

#print axioms euclidean_operator_norm_le_frobenius
#print axioms operator_probability_tendsto_of_frobenius
end SpectralRadiusUpperTail
