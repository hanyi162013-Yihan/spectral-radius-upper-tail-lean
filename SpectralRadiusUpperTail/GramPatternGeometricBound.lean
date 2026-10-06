import SpectralRadiusUpperTail.GramPatternMomentBound
import SpectralRadiusUpperTail.DefectGeometricAlgebra

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
attribute [local instance] Classical.propDecidable

noncomputable def gramDefectRatio (μ : Measure 𝕂) (c : ℝ) (m q n : ℕ) : ℝ :=
  (gramDefectCountBase m q : ℝ) * (signedWordMomentBase μ c (2*(q*m)))^6 / n

lemma gramPatternWeight_sum_le_geometric (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun z : 𝕂 => Real.exp (c*‖z‖^2)) μ)
    (hm : (∫ z : 𝕂, z ∂μ) = 0) (hv : (∫ z : 𝕂, ‖z‖^2 ∂μ) = 1)
    (m q n : ℕ) (hq : 1 ≤ q) (hn : 0 < n) :
    ∑ R : Setoid (Fin (2*(q*m)+1)), closedPatternWeight μ (gramTreeSign m q) n R ≤
      (m+1 : ℝ)^(2*q) * (n : ℝ)^(q*m+1) *
        ∑ g : Fin (q*m+1), (gramDefectRatio μ c m q n)^g.val := by
  apply (gramPatternWeight_sum_le μ c hc hexp hm hv m q n hq).trans_eq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g _
  rw [mul_assoc]
  rw [defect_weight_geometric (n : ℝ) _ _ (by exact_mod_cast hn) (q*m) g.val (by omega)]
  simp only [gramDefectRatio]
  ring

lemma gramPatternWeight_sum_le_two (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun z : 𝕂 => Real.exp (c*‖z‖^2)) μ)
    (hm : (∫ z : 𝕂, z ∂μ) = 0) (hv : (∫ z : 𝕂, ‖z‖^2 ∂μ) = 1)
    (m q n : ℕ) (hq : 1 ≤ q) (hn : 0 < n)
    (hr : gramDefectRatio μ c m q n ≤ 1/2) :
    ∑ R : Setoid (Fin (2*(q*m)+1)), closedPatternWeight μ (gramTreeSign m q) n R ≤
      2*(m+1 : ℝ)^(2*q) * (n : ℝ)^(q*m+1) := by
  apply (gramPatternWeight_sum_le_geometric μ c hc hexp hm hv m q n hq hn).trans
  have ha : 0 ≤ signedWordMomentBase μ c (2*(q*m)) :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (signedWordMomentBase_one_le μ c hc _)
  have hnon : 0 ≤ gramDefectRatio μ c m q n :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg ha 6)) (Nat.cast_nonneg _)
  have hh := mul_le_mul_of_nonneg_left
    (finite_geometric_sum_le_two _ hnon hr (q*m))
    (show 0 ≤ (m+1 : ℝ)^(2*q)*(n : ℝ)^(q*m+1) by positivity)
  convert hh using 1 <;> ring

#print axioms gramDefectRatio
#print axioms gramPatternWeight_sum_le_geometric
#print axioms gramPatternWeight_sum_le_two
end SpectralRadiusUpperTail
