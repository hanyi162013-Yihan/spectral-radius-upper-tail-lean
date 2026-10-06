import SpectralRadiusUpperTail.GaussianTruncatedMatrixConfidence
import SpectralRadiusUpperTail.GaussianLogarithmicCutoff

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped MeasureTheory Topology Matrix.Norms.L2Operator
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂]
attribute [local instance] matrixL2RealNormedAlgebra

/-- Explicit logarithmic confidence threshold for the actual truncated error. -/
noncomputable def gaussianLogConfidenceThreshold (μ : Measure 𝕂) (a d A B L : ℝ) (n : ℕ) : ℝ :=
  let V := (12*gaussianTruncationScale μ a d (A*Real.sqrt (Real.log (n : ℝ)))*
    gaussianLocalMomentCost μ d)*(L/Real.sqrt (n : ℝ))
  let b := 2*(B*Real.sqrt (Real.log (n : ℝ))+1)/Real.sqrt (n : ℝ)
  4*Real.sqrt (V*(2*Real.log (n : ℝ)))+8*b*(2*Real.log (n : ℝ))

/-- At logarithmic cutoffs the actual norm exceeds the explicit threshold
with probability at most 4/n, eventually, under original entry and flatness assumptions. -/
theorem gaussianLogConfidence_eventually (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (hm : (∫ x : 𝕂, x ∂μ) = 0)
    (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1) (a d : ℝ) (ha : 0 < a) (hd : 0 < d)
    (hexp : Integrable (fun x : 𝕂 => Real.exp (4*d*‖x‖^2)) μ)
    (A B L : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (v : ℕ → ℕ → 𝕂) (hv : ∀ n, ∑ j : Fin n, ‖v n j.val‖^2 ≤ 1)
    (hflat : ∀ n, ∀ j : Fin n, ‖v n j.val‖ ≤ L/Real.sqrt (n : ℝ))
    (t : (n : ℕ) → Fin n → 𝕂) :
    ∀ᶠ n : ℕ in atTop, (gaussianSequentialMatrixLaw μ (v n) a (t n)).real
      {x | gaussianLogConfidenceThreshold μ a d A B L n ≤
        ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := 𝕂)
          (gaussianTruncatedMatrix μ (v n) a (t n)
            (A*Real.sqrt (Real.log (n : ℝ))) (B*Real.sqrt (Real.log (n : ℝ))) x)‖} ≤
      4/(n : ℝ) := by
  filter_upwards [gaussianLogarithmicCutoff_smallness μ a d A L,
    eventually_ge_atTop (2 : ℕ)] with n hn hn2
  have hn0 : 0 < n := by omega
  have : NeZero n := ⟨Nat.ne_of_gt hn0⟩
  have hnr : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hnpos : (0 : ℝ) < n := lt_trans zero_lt_one hnr
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hnr
  have hR : 0 ≤ B*Real.sqrt (Real.log (n : ℝ)) := mul_nonneg hB (Real.sqrt_nonneg _)
  let b := 2*(B*Real.sqrt (Real.log (n : ℝ))+1)/Real.sqrt (n : ℝ)
  have hb : 0 < b := div_pos (by nlinarith) hsqrt
  have hbnd : 2*(B*Real.sqrt (Real.log (n : ℝ)))/Real.sqrt (n : ℝ) ≤ b := by
    apply div_le_div_of_nonneg_right _ hsqrt.le
    linarith
  have hh := gaussianTruncatedMatrix_confidence μ hX hm hvar (v n) (hv n) a d ha hd hexp
    (t n) (A*Real.sqrt (Real.log (n : ℝ))) (L/Real.sqrt (n : ℝ))
    (B*Real.sqrt (Real.log (n : ℝ))) (mul_nonneg hA (Real.sqrt_nonneg _))
    (div_nonneg hL hsqrt.le) hn.1 hR (hflat n) hn.2.1 hn.2.2 b hb hbnd
    (2*Real.log (n : ℝ)) (by positivity)
  have he : (4*(n : ℝ))*Real.exp (-(2*Real.log (n : ℝ))) = 4/(n : ℝ) := by
    rw [Real.exp_neg, show (2 : ℝ)*Real.log (n : ℝ) = (2 : ℕ)*Real.log (n : ℝ) from rfl,
      Real.exp_nat_mul, Real.exp_log hnpos]
    field_simp
  rw [he] at hh
  exact hh

#print axioms gaussianLogConfidence_eventually
end SpectralRadiusUpperTail
