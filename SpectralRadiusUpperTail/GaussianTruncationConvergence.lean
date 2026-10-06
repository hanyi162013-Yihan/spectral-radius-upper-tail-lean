import SpectralRadiusUpperTail.GaussianMatrixTruncationProbability
import SpectralRadiusUpperTail.GaussianLogarithmicCutoff

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped BigOperators Topology
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂]

/-- On the actual fixed coupling, the original centered matrix and its
logarithmically truncated/stopped matrix differ by o_P(n^(-1/2)). Both
exceptional probabilities and all smallness conditions are proved here. -/
theorem gaussianCenteredMatrix_logarithmic_approximation
    (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (hm : (∫ x : 𝕂, x ∂μ) = 0)
    (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1) (a d : ℝ) (ha : 0 < a) (hd : 0 < d)
    (hexp : Integrable (fun x : 𝕂 => Real.exp (4*d*‖x‖^2)) μ)
    (A B L H : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hAc : 2 < (rowSquareExpExponent (4*d)
      (∫ x : 𝕂, Real.exp (4*d*‖x‖^2) ∂μ)/2)*A^2)
    (hBc : 2 < (d/16)*B^2)
    (v : ℕ → ℕ → 𝕂) (hv : ∀ n, ∑ j : Fin n, ‖v n j.val‖^2 ≤ 1)
    (hflat : ∀ n, ∀ j : Fin n, ‖v n j.val‖ ≤ L/Real.sqrt (n : ℝ))
    (t : (n : ℕ) → Fin n → 𝕂) (ht : ∀ n i, ‖t n i‖ ≤ H)
    (r : ℝ) (hr : 0 < r) :
    Tendsto (fun n => (gaussianSequentialMatrixLaw μ (v n) a (t n)).real
      {x | r/Real.sqrt (n : ℝ) ≤ ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := 𝕂)
        (gaussianCenteredMatrix μ a (v n) (t n)
          (fun i => coordinateVector Prod.fst n (x i)) (fun i => comparatorVector n (x i))-
          gaussianTruncatedMatrix μ (v n) a (t n)
            (A*Real.sqrt (Real.log (n : ℝ))) (B*Real.sqrt (Real.log (n : ℝ))) x)‖})
      atTop (𝓝 0) := by
  let c := rowSquareExpExponent (4*d) (∫ x : 𝕂, Real.exp (4*d*‖x‖^2) ∂μ)
  let M := 2*Real.exp ((H^2+1)/a+c*H^2)
  have hb := matrixBadPrefix_logarithmic_bound_tendsto c A M hAc
  have he := (gaussianTruncationTail_logarithmic_tendsto μ d B 2 hBc).div_const (r^2)
  have hlim := hb.add he
  simp only [zero_div, zero_add] at hlim
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) ?_ hlim
  filter_upwards [gaussianLogarithmicCutoff_smallness μ a d A L,
    eventually_ge_atTop (1 : ℕ)] with n hs hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  have hK : 0 ≤ A*Real.sqrt (Real.log (n : ℝ)) := mul_nonneg hA (Real.sqrt_nonneg _)
  have hR : 0 ≤ B*Real.sqrt (Real.log (n : ℝ)) := mul_nonneg hB (Real.sqrt_nonneg _)
  have hh := gaussianCenteredMatrix_truncation_probability_le μ hX hm hvar (v n) (hv n)
    a d ha hd hexp (t n) (A*Real.sqrt (Real.log (n : ℝ))) (L/Real.sqrt (n : ℝ))
    (B*Real.sqrt (Real.log (n : ℝ))) hK hs.1 hR (hflat n) hs.2.1 hs.2.2
    (r/Real.sqrt (n : ℝ)) (div_pos hr hsn)
  have hp := gaussianMatrix_bad_prefix_probability μ hm hvar (4*d) (by positivity) hexp
    (v n) (hv n) a ha (t n) H (ht n) (A*Real.sqrt (Real.log (n : ℝ))) hK
  have halg : ((n : ℝ)*gaussianTruncationTail μ d (B*Real.sqrt (Real.log (n : ℝ)))) /
      (r/Real.sqrt (n : ℝ))^2 =
      (n : ℝ)^2*gaussianTruncationTail μ d (B*Real.sqrt (Real.log (n : ℝ)))/r^2 := by
    rw [div_pow, Real.sq_sqrt hnpos.le]
    field_simp
    <;> ring
  rw [halg] at hh
  exact hh.trans (add_le_add hp le_rfl)

#print axioms gaussianCenteredMatrix_logarithmic_approximation
end SpectralRadiusUpperTail
