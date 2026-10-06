import SpectralRadiusUpperTail.GaussianLogConfidenceCalibration

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped MeasureTheory Topology Matrix.Norms.L2Operator
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂]
attribute [local instance] matrixL2RealNormedAlgebra

/-- Actual truncated error has a fixed multiple of the target rate with failure at most 4/n. -/
theorem gaussianLogQuarterRate_eventually (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (hm : (∫ x : 𝕂, x ∂μ) = 0)
    (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1) (a d : ℝ) (ha : 0 < a) (hd : 0 < d)
    (hexp : Integrable (fun x : 𝕂 => Real.exp (4*d*‖x‖^2)) μ)
    (A B L : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (v : ℕ → ℕ → 𝕂) (hv : ∀ n, ∑ j : Fin n, ‖v n j.val‖^2 ≤ 1)
    (hflat : ∀ n, ∀ j : Fin n, ‖v n j.val‖ ≤ L/Real.sqrt (n : ℝ))
    (t : (n : ℕ) → Fin n → 𝕂) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, (gaussianSequentialMatrixLaw μ (v n) a (t n)).real
      {x | C*logQuarterRate n ≤
        ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := 𝕂)
          (gaussianTruncatedMatrix μ (v n) a (t n)
            (A*Real.sqrt (Real.log (n : ℝ))) (B*Real.sqrt (Real.log (n : ℝ))) x)‖} ≤
      4/(n : ℝ) := by
  obtain ⟨C, hC, hcal⟩ := gaussianLogConfidenceThreshold_calibration μ a d A B L hA hB hL
  refine ⟨C, hC, ?_⟩
  filter_upwards [hcal, gaussianLogConfidence_eventually μ hX hm hvar a d ha hd hexp
    A B L hA hB hL v hv hflat t] with n hn hp
  have : IsProbabilityMeasure (gaussianSequentialMatrixLaw μ (v n) a (t n)) :=
    gaussianSequentialMatrixLaw_probability μ (v n) a ha (t n)
  apply le_trans (measureReal_mono ?_) hp
  intro x hx
  exact hn.trans hx

#print axioms gaussianLogQuarterRate_eventually
end SpectralRadiusUpperTail
