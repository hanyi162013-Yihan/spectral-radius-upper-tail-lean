import SpectralRadiusUpperTail.GaussianTruncationConvergence
import SpectralRadiusUpperTail.GaussianLogQuarterRateLimit
import SpectralRadiusUpperTail.LogQuarterComparison

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped BigOperators Topology
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂]

/-- The original centered error on the actual coupling has the target quarter-power rate. -/
theorem gaussianCenteredMatrix_quarter_rate
    (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (hm : (∫ x : 𝕂, x ∂μ) = 0)
    (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1) (a d : ℝ) (ha : 0 < a) (hd : 0 < d)
    (hexp : Integrable (fun x : 𝕂 => Real.exp (4*d*‖x‖^2)) μ)
    (A B L H : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hAc : 2 < (rowSquareExpExponent (4*d)
      (∫ x : 𝕂, Real.exp (4*d*‖x‖^2) ∂μ)/2)*A^2)
    (hBc : 2 < (d/16)*B^2)
    (v : ℕ → ℕ → 𝕂) (hv : ∀ n, ∑ j : Fin n, ‖v n j.val‖^2 ≤ 1)
    (hflat : ∀ n, ∀ j : Fin n, ‖v n j.val‖ ≤ L/Real.sqrt (n : ℝ))
    (t : (n : ℕ) → Fin n → 𝕂) (ht : ∀ n i, ‖t n i‖ ≤ H)
    :
    ∃ C : ℝ, 0 < C ∧ Tendsto (fun n => (gaussianSequentialMatrixLaw μ (v n) a (t n)).real
      {x | C*logQuarterRate n ≤ ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := 𝕂)
        (gaussianCenteredMatrix μ a (v n) (t n)
          (fun i => coordinateVector Prod.fst n (x i)) (fun i => comparatorVector n (x i)))‖})
      atTop (𝓝 0) := by
  obtain ⟨C, hC, htr⟩ := gaussianLogQuarterRate_probability_tendsto μ hX hm hvar
    a d ha hd hexp A B L hA hB hL v hv hflat t
  have happ := gaussianCenteredMatrix_logarithmic_approximation μ hX hm hvar
    a d ha hd hexp A B L H hA hB hAc hBc v hv hflat t ht 1 zero_lt_one
  have hlim := happ.add htr
  simp only [zero_add] at hlim
  refine ⟨C+1, by linarith, ?_⟩
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) ?_ hlim
  filter_upwards [logQuarterRate_inv_sqrt_eventually] with n hn
  have : IsProbabilityMeasure (gaussianSequentialMatrixLaw μ (v n) a (t n)) :=
    gaussianSequentialMatrixLaw_probability μ (v n) a ha (t n)
  apply le_trans (measureReal_mono ?_) (measureReal_union_le _ _)
  intro x hx
  let F := gaussianCenteredMatrix μ a (v n) (t n)
    (fun i => coordinateVector Prod.fst n (x i)) (fun i => comparatorVector n (x i))
  let G := gaussianTruncatedMatrix μ (v n) a (t n)
    (A*Real.sqrt (Real.log (n : ℝ))) (B*Real.sqrt (Real.log (n : ℝ))) x
  let T := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := 𝕂)
  change (1/Real.sqrt (n : ℝ) ≤ ‖T (F-G)‖) ∨ (C*logQuarterRate n ≤ ‖T G‖)
  change (C+1)*logQuarterRate n ≤ ‖T F‖ at hx
  by_contra hh
  push_neg at hh
  have hnorm := norm_add_le (T (F-G)) (T G)
  rw [← map_add, sub_add_cancel] at hnorm
  nlinarith [add_lt_add hh.1 hh.2]

#print axioms gaussianCenteredMatrix_quarter_rate
end SpectralRadiusUpperTail
