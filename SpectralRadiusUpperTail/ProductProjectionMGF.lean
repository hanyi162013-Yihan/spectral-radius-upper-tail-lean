import SpectralRadiusUpperTail.SquareExpMGF
import Mathlib.MeasureTheory.Integral.Pi

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators

lemma squareExpMgfConstant_pos (τ M : ℝ) (hτ : 0 < τ) (hM : 0 ≤ M) :
    0 < squareExpMgfConstant τ M := by
  dsimp [squareExpMgfConstant]
  positivity

variable {E ι : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

/-- Scaling keeps the MGF proxy quadratic in the projection size. -/
theorem squareExp_scaled_projection_mgf (μ : Measure E) [IsProbabilityMeasure μ]
    (X : E → ℝ) (hX : Measurable X) (hXi : Integrable X μ)
    (hmean : (∫ x, X x ∂μ) = 0) (b : ℝ) (hb : 0 ≤ b)
    (hbound : ∀ x, |X x| ≤ b*‖x‖) (τ : ℝ) (hτ : 0 < τ)
    (hexp : Integrable (fun x : E => Real.exp (τ*‖x‖^2)) μ) (t : ℝ) :
    Integrable (fun x => Real.exp (t*X x)) μ ∧
      (∫ x, Real.exp (t*X x) ∂μ) ≤
        Real.exp (squareExpMgfConstant τ (∫ x : E, Real.exp (τ*‖x‖^2) ∂μ)*b^2*t^2) := by
  by_cases hb0 : b = 0
  · have hx (x : E) : X x = 0 := abs_eq_zero.mp
      (le_antisymm (by simpa [hb0] using hbound x) (abs_nonneg _))
    simp_rw [hx, hb0, mul_zero, Real.exp_zero]
    exact ⟨integrable_const 1, by simp⟩
  · have hbp : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    have hmean' : (∫ x, X x/b ∂μ) = 0 := by rw [integral_div, hmean, zero_div]
    have hb' (x : E) : |X x/b| ≤ ‖x‖ := by
      rw [abs_div, abs_of_pos hbp]
      apply (div_le_iff₀ hbp).mpr
      simpa only [mul_comm] using hbound x
    have h := squareExp_projected_mgf μ (fun x => X x/b) (hX.div_const b)
      (hXi.div_const b) hmean' hb' τ hτ hexp (t*b)
    have he : (fun x => Real.exp ((t*b)*(X x/b))) = (fun x => Real.exp (t*X x)) := by
      funext x
      congr 1
      field_simp
    rw [he] at h
    refine ⟨h.1, h.2.trans_eq ?_⟩
    congr 1
    ring

variable [Fintype ι]

/-- Every finite product of centered norm-dominated projections has the same
quadratic MGF constant when the projection-size squares sum to at most one. -/
theorem product_projection_mgf (μ : Measure E) [IsProbabilityMeasure μ]
    (X : ι → E → ℝ) (hX : ∀ i, Measurable (X i)) (hXi : ∀ i, Integrable (X i) μ)
    (hmean : ∀ i, (∫ x, X i x ∂μ) = 0) (b : ι → ℝ) (hb : ∀ i, 0 ≤ b i)
    (hbound : ∀ i x, |X i x| ≤ b i*‖x‖) (hb2 : ∑ i, (b i)^2 ≤ 1)
    (τ : ℝ) (hτ : 0 < τ)
    (hexp : Integrable (fun x : E => Real.exp (τ*‖x‖^2)) μ) (t : ℝ) :
    Integrable (fun s : ι → E => Real.exp (t*∑ i, X i (s i))) (Measure.pi (fun _ : ι => μ)) ∧
      (∫ s, Real.exp (t*∑ i, X i (s i)) ∂Measure.pi (fun _ : ι => μ)) ≤
        Real.exp (squareExpMgfConstant τ (∫ x : E, Real.exp (τ*‖x‖^2) ∂μ)*t^2) := by
  let K := squareExpMgfConstant τ (∫ x : E, Real.exp (τ*‖x‖^2) ∂μ)
  have hK : 0 ≤ K := (squareExpMgfConstant_pos τ _ hτ
    (integral_nonneg (fun _ => Real.exp_nonneg _))).le
  have hi (i : ι) := squareExp_scaled_projection_mgf μ (X i) (hX i) (hXi i)
    (hmean i) (b i) (hb i) (hbound i) τ hτ hexp t
  have he (s : ι → E) : Real.exp (t*∑ i, X i (s i)) = ∏ i, Real.exp (t*X i (s i)) := by
    rw [Finset.mul_sum, Real.exp_sum]
  refine ⟨?_, ?_⟩
  · simp_rw [he]
    exact Integrable.fintype_prod (fun i => (hi i).1)
  · simp_rw [he]
    rw [integral_fintype_prod_eq_prod (fun i x => Real.exp (t*X i x))]
    calc
      _ ≤ ∏ i, Real.exp (K*(b i)^2*t^2) := by
        apply Finset.prod_le_prod
        · intro i _
          exact integral_nonneg (fun _ => Real.exp_nonneg _)
        · intro i _
          exact (hi i).2
      _ = Real.exp (K*(∑ i, (b i)^2)*t^2) := by
        rw [← Real.exp_sum]
        congr 1
        simp only [Finset.mul_sum, Finset.sum_mul]
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb2 hK) (sq_nonneg t)
        simpa only [mul_one] using h

#print axioms product_projection_mgf
end SpectralRadiusUpperTail
