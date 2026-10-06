import SpectralRadiusUpperTail.PairedPathIntegral
import SpectralRadiusUpperTail.PairedAssignmentSumBound
import SpectralRadiusUpperTail.ConjugateSecondMoment

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
variable {k n : ℕ}

lemma iidPowerBilinear_mul_star_integrable (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c)
    (hexp : Integrable (fun z : 𝕂 => Real.exp (c*‖z‖^2)) μ)
    (p q : Fin n → 𝕂) (k : ℕ) :
    Integrable (fun y : Fin n × Fin n → 𝕂 =>
      (∑ i, star (p i) * ((Matrix.of (fun i j => y (i,j)))^k).mulVec q i) *
        star (∑ i, star (p i) * ((Matrix.of (fun i j => y (i,j)))^k).mulVec q i))
      (Measure.pi (fun _ : Fin n × Fin n => μ)) := by
  classical
  simp_rw [matrixBilinear_pair_expansion]
  exact integrable_finsetSum _ (fun x _ => pairedPathTerm_integrable μ c hc hexp p q x)

/-- The actual unnormalized iid power bilinear second moment, expressed as
an integral of the form times its conjugate, is bounded by the pattern sum. -/
lemma iidPowerBilinear_integral_norm_le (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c)
    (hexp : Integrable (fun z : 𝕂 => Real.exp (c*‖z‖^2)) μ)
    (hm : (∫ z : 𝕂, z ∂μ) = 0) (hk : 0 < k) (hn : 0 < n)
    (p q : Fin n → 𝕂) (hp : (∑ i, ‖p i‖^2) ≤ 1) (hq : (∑ i, ‖q i‖^2) ≤ 1) :
    ‖∫ y : Fin n × Fin n → 𝕂,
      (∑ i, star (p i) * ((Matrix.of (fun i j => y (i,j)))^k).mulVec q i) *
        star (∑ i, star (p i) * ((Matrix.of (fun i j => y (i,j)))^k).mulVec q i)
      ∂Measure.pi (fun _ : Fin n × Fin n => μ)‖ ≤
    pairedMomentConstant μ k * (n : ℝ)^(k-1) := by
  classical
  simp_rw [matrixBilinear_pair_expansion]
  rw [integral_finsetSum _ (fun x _ => pairedPathTerm_integrable μ c hc hexp p q x)]
  calc
    _ ≤ ∑ x : (Fin (k+1) ⊕ Fin (k+1)) → Fin n,
        ‖∫ y : Fin n × Fin n → 𝕂,
          matrixBilinearPathTerm (Matrix.of (fun i j => y (i,j))) p q k
            (fun a => x (Sum.inl a)) *
          star (matrixBilinearPathTerm (Matrix.of (fun i j => y (i,j))) p q k
            (fun a => x (Sum.inr a))) ∂Measure.pi (fun _ : Fin n × Fin n => μ)‖ :=
      norm_sum_le _ _
    _ = ∑ x : (Fin (k+1) ⊕ Fin (k+1)) → Fin n,
        pairedAssignmentWeight p q x * ‖pairedAssignmentMoment μ x‖ := by
      apply Finset.sum_congr rfl
      intro x _
      exact pairedPathTerm_integral_norm μ p q x
    _ ≤ _ := pairedAssignment_total_bound μ hm hk hn p q hp hq

lemma iidPowerBilinear_secondMoment_le (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c)
    (hexp : Integrable (fun z : 𝕂 => Real.exp (c*‖z‖^2)) μ)
    (hm : (∫ z : 𝕂, z ∂μ) = 0) (hk : 0 < k) (hn : 0 < n)
    (p q : Fin n → 𝕂) (hp : (∑ i, ‖p i‖^2) ≤ 1) (hq : (∑ i, ‖q i‖^2) ≤ 1) :
    (∫ y : Fin n × Fin n → 𝕂,
      ‖∑ i, star (p i) * ((Matrix.of (fun i j => y (i,j)))^k).mulVec q i‖^2
      ∂Measure.pi (fun _ : Fin n × Fin n => μ)) ≤
    pairedMomentConstant μ k * (n : ℝ)^(k-1) := by
  exact (integral_norm_sq_le_norm_integral_mul_star
    (iidPowerBilinear_mul_star_integrable μ c hc hexp p q k)).trans
      (iidPowerBilinear_integral_norm_le μ c hc hexp hm hk hn p q hp hq)

#print axioms iidPowerBilinear_mul_star_integrable
#print axioms iidPowerBilinear_secondMoment_le
#print axioms iidPowerBilinear_integral_norm_le
end SpectralRadiusUpperTail
