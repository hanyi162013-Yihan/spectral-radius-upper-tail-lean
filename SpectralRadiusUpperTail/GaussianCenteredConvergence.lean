import SpectralRadiusUpperTail.GaussianCenteredQuarterRate
import SpectralRadiusUpperTail.RegressionTailLimit

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped BigOperators Topology
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂]

lemma exists_nonneg_cutoff_square (c : ℝ) (hc : 0 < c) :
    ∃ A : ℝ, 0 ≤ A ∧ 2 < c*A^2 := by
  refine ⟨Real.sqrt (3/c), Real.sqrt_nonneg _, ?_⟩
  rw [Real.sq_sqrt (by positivity)]
  have he : c*(3/c) = 3 := by field_simp
  rw [he]
  norm_num

/-- Fixed-threshold convergence under original entry assumptions; auxiliary cutoffs are chosen internally. -/
theorem gaussianCenteredMatrix_probability_tendsto
    (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hm : (∫ x : 𝕂, x ∂μ) = 0)
    (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1) (a d : ℝ) (ha : 0 < a) (hd : 0 < d)
    (hexp : Integrable (fun x : 𝕂 => Real.exp (4*d*‖x‖^2)) μ)
    (L H : ℝ) (hL : 0 ≤ L)
    (v : ℕ → ℕ → 𝕂) (hv : ∀ n, ∑ j : Fin n, ‖v n j.val‖^2 ≤ 1)
    (hflat : ∀ n, ∀ j : Fin n, ‖v n j.val‖ ≤ L/Real.sqrt (n : ℝ))
    (t : (n : ℕ) → Fin n → 𝕂) (ht : ∀ n i, ‖t n i‖ ≤ H)
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => (gaussianSequentialMatrixLaw μ (v n) a (t n)).real
      {x | ε ≤ ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := 𝕂)
        (gaussianCenteredMatrix μ a (v n) (t n)
          (fun i => coordinateVector Prod.fst n (x i)) (fun i => comparatorVector n (x i)))‖})
      atTop (𝓝 0) := by
  have hX : MemLp (fun x : 𝕂 => x) 2 μ :=
    (memLp_two_iff_integrable_sq_norm (by fun_prop)).mpr
      (squareExp_norm_pow_integrable μ (4*d) (by positivity) hexp 2)
  have hc : 0 < rowSquareExpExponent (4*d)
      (∫ x : 𝕂, Real.exp (4*d*‖x‖^2) ∂μ) :=
    rowSquareExpExponent_pos _ _ (by positivity) (integral_nonneg (fun _ => (Real.exp_pos _).le))
  obtain ⟨A, hA, hAc⟩ := exists_nonneg_cutoff_square
    (rowSquareExpExponent (4*d) (∫ x : 𝕂, Real.exp (4*d*‖x‖^2) ∂μ)/2) (by positivity)
  obtain ⟨B, hB, hBc⟩ := exists_nonneg_cutoff_square (d/16) (by positivity)
  obtain ⟨C, hC, hprob⟩ := gaussianCenteredMatrix_quarter_rate μ hX hm hvar a d ha hd hexp
    A B L H hA hB hL hAc hBc v hv hflat t ht
  have hlim : Tendsto (fun n => C*logQuarterRate n) atTop (𝓝 0) := by
    simpa using logQuarterRate_tendsto.const_mul C
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) ?_ hprob
  filter_upwards [hlim.eventually (Iio_mem_nhds hε)] with n hn
  have : IsProbabilityMeasure (gaussianSequentialMatrixLaw μ (v n) a (t n)) :=
    gaussianSequentialMatrixLaw_probability μ (v n) a ha (t n)
  exact measureReal_mono (fun x hx => hn.le.trans hx)

#print axioms exists_nonneg_cutoff_square
#print axioms gaussianCenteredMatrix_probability_tendsto
end SpectralRadiusUpperTail
