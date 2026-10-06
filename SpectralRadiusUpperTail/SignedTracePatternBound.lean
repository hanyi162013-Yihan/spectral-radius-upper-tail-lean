import SpectralRadiusUpperTail.SignedTraceAssignmentBound
import SpectralRadiusUpperTail.ClosedAssignmentPatternBound
import SpectralRadiusUpperTail.ClosedPatternWeightedSum

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {ι 𝕂 : Type*} [Fintype ι] [DecidableEq ι] [RCLike 𝕂]
  [MeasurableSpace 𝕂] [BorelSpace 𝕂]

lemma signedTrace_integral_eq_assignments_length {n : ℕ}
    (μ : Measure 𝕂) [IsProbabilityMeasure μ] (c : ℝ) (hc : 0 < c)
    (hexp : Integrable (fun z : 𝕂 => Real.exp (c*‖z‖^2)) μ)
    (L : List Bool) (h : L.length = n) :
    (∫ x : ι × ι → 𝕂,
      (L.map (signedMatrixFactor (Matrix.of (fun i j => x (i,j))))).prod.trace
      ∂Measure.pi (fun _ : ι × ι => μ)) =
    ∑ v : Fin (n+1) → ι,
      orientedAssignmentMoment μ (fun a => L.get (Fin.cast h.symm a)) v *
        (1 : Matrix ι ι 𝕂) (v (Fin.last n)) (v 0) := by
  subst n
  exact signedTrace_integral_eq_assignments μ c hc hexp L

lemma signedTrace_integral_norm_le_patterns {r : ℕ}
    (μ : Measure 𝕂) [IsProbabilityMeasure μ] (c : ℝ) (hc : 0 < c)
    (hexp : Integrable (fun z : 𝕂 => Real.exp (c*‖z‖^2)) μ)
    (L : List Bool) (h : L.length = 2*r) :
    ‖∫ x : ι × ι → 𝕂,
      (L.map (signedMatrixFactor (Matrix.of (fun i j => x (i,j))))).prod.trace
      ∂Measure.pi (fun _ : ι × ι => μ)‖ ≤
    ∑ R : Setoid (Fin (2*r+1)), closedPatternWeight μ
      (fun a => L.get (Fin.cast h.symm a)) (Fintype.card ι) R := by
  classical
  let s : Fin (2*r) → Bool := fun a => L.get (Fin.cast h.symm a)
  rw [signedTrace_integral_eq_assignments_length μ c hc hexp L h]
  calc
    _ ≤ ∑ v : Fin (2*r+1) → ι, closedAssignmentWeight μ s v := by
      apply (norm_sum_le Finset.univ (fun v : Fin (2*r+1) → ι =>
        orientedAssignmentMoment μ s v * (1 : Matrix ι ι 𝕂)
          (v (Fin.last (2*r))) (v 0))).trans
      apply Finset.sum_le_sum
      intro v _
      by_cases hv : v (Fin.last (2*r)) = v 0
      · have hi : (1 : Matrix ι ι 𝕂) (v (Fin.last (2*r))) (v 0) = 1 := by
          rw [hv]
          exact Matrix.one_apply_eq _
        simp only [closedAssignmentWeight,if_pos hv,hi,mul_one,le_refl]
      · simp [closedAssignmentWeight,hv,Matrix.one_apply_ne hv]
    _ = ∑ R : Setoid (Fin (2*r+1)), equalityPatternContribution R
        (closedAssignmentWeight (ι := ι) μ s) := sum_eq_equalityPatterns _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro R _
      have hh := closedAssignmentPatternContribution_le (ι := ι) μ s R
      simpa only [closedPatternWeight,mul_ite,mul_zero] using hh

#print axioms signedTrace_integral_eq_assignments_length
#print axioms signedTrace_integral_norm_le_patterns
end SpectralRadiusUpperTail
