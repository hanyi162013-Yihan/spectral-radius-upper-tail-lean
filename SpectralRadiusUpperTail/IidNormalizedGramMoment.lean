import SpectralRadiusUpperTail.IidGramPatternBound
import SpectralRadiusUpperTail.MatrixTraceScaling

namespace SpectralRadiusUpperTail
open MeasureTheory
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]

noncomputable def normalizedIidMatrix {n : ℕ} (x : Fin n × Fin n → 𝕂) : Matrix (Fin n) (Fin n) 𝕂 :=
  (((1/Real.sqrt (n : ℝ) : ℝ) : 𝕂) • Matrix.of (fun i j => x (i,j)))

lemma normalizedGramTraceMoment_integrable (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun z : 𝕂 => Real.exp (c*‖z‖^2)) μ)
    (m q n : ℕ) :
    Integrable (fun x : Fin n × Fin n → 𝕂 => matrixTraceMoment q ((normalizedIidMatrix x)^m))
      (Measure.pi (fun _ : Fin n × Fin n => μ)) := by
  simp_rw [normalizedIidMatrix,normalized_matrixTraceMoment_power]
  exact (iidGramTraceMoment_integrable μ c hc hexp m q).const_mul _

lemma normalizedGramTraceMoment_le_two (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun z : 𝕂 => Real.exp (c*‖z‖^2)) μ)
    (hm : (∫ z : 𝕂, z ∂μ) = 0) (hv : (∫ z : 𝕂, ‖z‖^2 ∂μ) = 1)
    (m q n : ℕ) (hq : 1 ≤ q) (hn : 0 < n) (hr : gramDefectRatio μ c m q n ≤ 1/2) :
    (∫ x : Fin n × Fin n → 𝕂, matrixTraceMoment q ((normalizedIidMatrix x)^m)
      ∂Measure.pi (fun _ : Fin n × Fin n => μ)) ≤ 2*(n : ℝ)*(m+1 : ℝ)^(2*q) := by
  simp_rw [normalizedIidMatrix,normalized_matrixTraceMoment_power]
  rw [integral_const_mul]
  have hh := iidGramTraceMoment_le_two (ι := Fin n) μ c hc hexp hm hv m q hq
    (by simpa only [Fintype.card_fin] using hn) (by simpa only [Fintype.card_fin] using hr)
  simp only [Fintype.card_fin] at hh
  apply (mul_le_mul_of_nonneg_left hh (show 0 ≤ (1/(n : ℝ))^(q*m) by positivity)).trans_eq
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  rw [pow_succ,one_div,inv_pow]
  field_simp
  <;> ring

#print axioms normalizedIidMatrix
#print axioms normalizedGramTraceMoment_integrable
#print axioms normalizedGramTraceMoment_le_two
end SpectralRadiusUpperTail
