import SpectralRadiusUpperTail.IidComplexOpNormTail
import SpectralRadiusUpperTail.ExponentialPrefactorBudget

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

lemma iid_complex_opNorm_exponential_tightness (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hXi : Integrable (fun x : ℂ => x) μ) (hm : (∫ x : ℂ, x ∂μ) = 0)
    (τ : ℝ) (hτ : 0 < τ) (hexp : Integrable (fun x : ℂ => Real.exp (τ*‖x‖^2)) μ)
    (r K : ℝ) (hK : 0 < K) :
    ∃ R : ℝ, r < R ∧ ∀ᶠ n : ℕ in atTop,
      (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real
        {x | R < ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (normalizedArray x)‖} ≤
          Real.exp (-K*(n : ℝ)) := by
  let c := rowSquareExpExponent τ (∫ x : ℂ, Real.exp (τ*‖x‖^2) ∂μ)
  have hc : 0 < c := (iid_row_squareExp μ (fun _ : Fin 0 => (0 : ℂ)) hXi hm
    (by simp) τ hτ hexp).1
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let B := K+Real.log 2+3
  have hB : 0 < B := by dsimp [B]; linarith
  let R := |r|+3+B/c
  have hdiv : 0 < B/c := div_pos hB hc
  have hR : 2 ≤ R := by dsimp [R]; linarith [abs_nonneg r]
  have hcR : B ≤ c*R := by
    have he : c*(B/c) = B := mul_div_cancel₀ B hc.ne'
    dsimp [R]
    nlinarith [mul_nonneg hc.le (abs_nonneg r)]
  have hrate : Real.log 2+2-c*R^2/2 ≤ -K-1 := by
    have hh := mul_le_mul_of_nonneg_left hR (mul_nonneg hc.le (by linarith : 0 ≤ R))
    dsimp [B] at hcR
    nlinarith
  refine ⟨R, ?_, ?_⟩
  · dsimp [R]
    linarith [le_abs_self r]
  · have hp := eventually_exp_prefactor_absorb 2 (-K-1) 1 (by norm_num) (by norm_num)
    filter_upwards [hp, eventually_gt_atTop 0] with n hn hn0
    have ht := iid_complex_opNorm_tail μ n hn0 hXi hm τ hτ hexp R (by linarith)
    apply ht.trans
    calc
      2*Real.exp ((n : ℝ)*(Real.log 2+2-c*R^2/2)) ≤
          2*Real.exp ((n : ℝ)*(-K-1)) := by
        gcongr
      _ ≤ Real.exp ((n : ℝ)*((-K-1)+1)) := hn
      _ = _ := by congr 1; ring

#print axioms iid_complex_opNorm_exponential_tightness
end SpectralRadiusUpperTail
