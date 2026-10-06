import SpectralRadiusUpperTail.GaussianLogConfidence

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped MeasureTheory Topology Matrix.Norms.L2Operator
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂]
attribute [local instance] matrixL2RealNormedAlgebra

/-- Actual probability of exceeding the logarithmic confidence threshold tends to zero. -/
theorem gaussianLogConfidence_probability_tendsto (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (hm : (∫ x : 𝕂, x ∂μ) = 0)
    (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1) (a d : ℝ) (ha : 0 < a) (hd : 0 < d)
    (hexp : Integrable (fun x : 𝕂 => Real.exp (4*d*‖x‖^2)) μ)
    (A B L : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (v : ℕ → ℕ → 𝕂) (hv : ∀ n, ∑ j : Fin n, ‖v n j.val‖^2 ≤ 1)
    (hflat : ∀ n, ∀ j : Fin n, ‖v n j.val‖ ≤ L/Real.sqrt (n : ℝ))
    (t : (n : ℕ) → Fin n → 𝕂) :
    Tendsto (fun n : ℕ => (gaussianSequentialMatrixLaw μ (v n) a (t n)).real
      {x | gaussianLogConfidenceThreshold μ a d A B L n ≤
        ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := 𝕂)
          (gaussianTruncatedMatrix μ (v n) a (t n)
            (A*Real.sqrt (Real.log (n : ℝ))) (B*Real.sqrt (Real.log (n : ℝ))) x)‖})
      atTop (𝓝 0) := by
  have hb := gaussianLogConfidence_eventually μ hX hm hvar a d ha hd hexp
    A B L hA hB hL v hv hflat t
  exact squeeze_zero' (Filter.Eventually.of_forall (fun _ => measureReal_nonneg)) hb
    (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)

#print axioms gaussianLogConfidence_probability_tendsto
end SpectralRadiusUpperTail
