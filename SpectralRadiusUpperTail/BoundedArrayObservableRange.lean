import SpectralRadiusUpperTail.LipschitzArrayIntegrable
import SpectralRadiusUpperTail.EntryCutoffLaw

namespace SpectralRadiusUpperTail
open MeasureTheory WithLp
open scoped BigOperators NNReal
variable {𝕂 : Type*} [RCLike 𝕂]

lemma bounded_square_array_norm (n : ℕ) (K : ℝ) (hK : 0 ≤ K)
    (x : Fin (n*n) → 𝕂) (hx : ∀ i, ‖x i‖ ≤ K) :
    ‖toLp 2 x‖ ≤ (n : ℝ)*K := by
  have hs : ‖toLp 2 x‖^2 ≤ (n : ℝ)^2*K^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc
      _ ≤ ∑ _i : Fin (n*n), K^2 := Finset.sum_le_sum (fun i _ =>
        (sq_le_sq₀ (norm_nonneg _) hK).mpr (hx i))
      _ = _ := by simp [pow_two]
  have hnK : 0 ≤ (n : ℝ)*K := mul_nonneg (Nat.cast_nonneg _) hK
  nlinarith [norm_nonneg (toLp 2 x)]

lemma bounded_normalized_lipschitz_range (n : ℕ) (hn : 0 < n)
    (K : ℝ) (hK : 0 ≤ K) (L : ℝ≥0)
    (f : EuclideanSpace 𝕂 (Fin (n*n)) → ℝ) (hf : LipschitzWith (L/(n : ℝ≥0)) f)
    (x : Fin (n*n) → 𝕂) (hx : ∀ i, ‖x i‖ ≤ K) :
    |f (toLp 2 x)-f 0| ≤ (L : ℝ)*K := by
  have hh := hf.norm_sub_le (toLp 2 x) 0
  simp only [sub_zero, Real.norm_eq_abs, NNReal.coe_div, NNReal.coe_natCast] at hh
  apply hh.trans
  calc
    _ ≤ ((L : ℝ)/(n : ℝ))*((n : ℝ)*K) :=
      mul_le_mul_of_nonneg_left (bounded_square_array_norm n K hK x hx) (by positivity)
    _ = _ := by field_simp

lemma cutoff_product_observable_range (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (n : ℕ) (hn : 0 < n) (K : ℕ) (L : ℝ≥0)
    (f : EuclideanSpace 𝕂 (Fin (n*n)) → ℝ) (hf : LipschitzWith (L/(n : ℝ≥0)) f) :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin (n*n) => μ.map (entryCutoff (K : ℝ))),
      |f (toLp 2 x)-f 0| ≤ (L : ℝ)*(K : ℝ) := by
  letI : IsProbabilityMeasure (μ.map (entryCutoff (K : ℝ))) :=
    Measure.isProbabilityMeasure_map (entryCutoff_measurable (K : ℝ)).aemeasurable
  have ha : ∀ᵐ x ∂Measure.pi (fun _ : Fin (n*n) => μ.map (entryCutoff (K : ℝ))),
      ∀ i, ‖x i‖ ≤ (K : ℝ) := by
    apply ae_all_iff.mpr
    intro i
    exact (measurePreserving_eval (fun _ : Fin (n*n) => μ.map (entryCutoff (K : ℝ))) i).quasiMeasurePreserving.ae (entryCutoff_law_supported μ (K : ℝ) (by positivity))
  filter_upwards [ha] with x hx
  exact bounded_normalized_lipschitz_range n hn (K : ℝ) (by positivity) L f hf x hx

#print axioms bounded_square_array_norm
#print axioms bounded_normalized_lipschitz_range
#print axioms cutoff_product_observable_range
end SpectralRadiusUpperTail
