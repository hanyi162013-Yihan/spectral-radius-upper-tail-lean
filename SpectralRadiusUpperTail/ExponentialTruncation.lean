import SpectralRadiusUpperTail.CenteredSquareExp
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace SpectralRadiusUpperTail
open MeasureTheory
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- The discarded second moment has an explicit Gaussian tail bound. -/
theorem squareExp_tail_secondMoment (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → E) (hX : Measurable X) (c M R : ℝ) (hc : 0 < c) (hR : 0 ≤ R)
    (he : Integrable (fun x => Real.exp (c*‖X x‖^2)) μ)
    (hM : (∫ x, Real.exp (c*‖X x‖^2) ∂μ) ≤ M) :
    (∫ x in {x | R < ‖X x‖}, ‖X x‖^2 ∂μ) ≤
      (2/c)*Real.exp (-(c/2)*R^2)*M := by
  classical
  have hset : MeasurableSet {x | R < ‖X x‖} := measurableSet_lt measurable_const hX.norm
  obtain ⟨_, h2⟩ := squareExp_moments μ X hX.aestronglyMeasurable c hc he
  have he2 (r : ℝ) : r^2 ≤ (2/c)*Real.exp ((c/2)*r^2) := by
    have hh := Real.add_one_le_exp ((c/2)*r^2)
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hc).mpr
    nlinarith
  have hb (x : Ω) :
      {y | R < ‖X y‖}.indicator (fun y => ‖X y‖^2) x ≤
        ((2/c)*Real.exp (-(c/2)*R^2))*Real.exp (c*‖X x‖^2) := by
    by_cases hx : R < ‖X x‖
    · simp only [Set.indicator_apply, Set.mem_ofPred_eq, hx, if_true]
      calc
        _ ≤ (2/c)*Real.exp ((c/2)*‖X x‖^2) := he2 _
        _ ≤ (2/c)*Real.exp (-(c/2)*R^2+c*‖X x‖^2) := by
          apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
          have hh : R^2 ≤ ‖X x‖^2 := sq_le_sq₀ hR (norm_nonneg _) |>.mpr hx.le
          nlinarith
        _ = _ := by rw [Real.exp_add]; ring
    · simp only [Set.indicator_apply, Set.mem_ofPred_eq, hx, if_false]
      positivity
  have hh := integral_mono (h2.indicator hset)
    (he.const_mul ((2/c)*Real.exp (-(c/2)*R^2))) hb
  rw [integral_indicator hset, integral_const_mul] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left hM (by positivity))

/-- Recenter a genuinely truncated mean-zero variable. Its pointwise size is at
most twice the cutoff, its variance does not increase, and the approximation
error is bounded by the actual discarded second moment. -/
theorem recentered_truncation_moments (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → E) (hX : Measurable X) (h1 : Integrable X μ)
    (h2 : Integrable (fun x => ‖X x‖^2) μ) (hm : (∫ x, X x ∂μ) = 0)
    (R : ℝ) (hR : 0 ≤ R) :
    let S := {x | ‖X x‖ ≤ R}
    let Y := S.indicator X
    let Z := fun x => Y x-∫ y, Y y ∂μ
    Integrable Z μ ∧ (∫ x, Z x ∂μ) = 0 ∧
      (∀ x, ‖Z x‖ ≤ 2*R) ∧
      (∫ x, ‖Z x‖^2 ∂μ) ≤ ∫ x, ‖X x‖^2 ∂μ ∧
      (∫ x, ‖X x-Z x‖^2 ∂μ) ≤ ∫ x in {x | R < ‖X x‖}, ‖X x‖^2 ∂μ := by
  classical
  let S := {x | ‖X x‖ ≤ R}
  let Y := S.indicator X
  let Q := Sᶜ.indicator X
  have hS : MeasurableSet S := measurableSet_le hX.norm measurable_const
  have hYi : Integrable Y μ := h1.indicator hS
  have hQi : Integrable Q μ := h1.indicator hS.compl
  have hYsq : (fun x => ‖Y x‖^2) = S.indicator (fun x => ‖X x‖^2) := by
    funext x
    by_cases hx : x ∈ S <;> simp [Y, hx]
  have hQsq : (fun x => ‖Q x‖^2) = Sᶜ.indicator (fun x => ‖X x‖^2) := by
    funext x
    by_cases hx : x ∈ Sᶜ <;> simp [Q, hx]
  have hY2 : Integrable (fun x => ‖Y x‖^2) μ := by rw [hYsq]; exact h2.indicator hS
  have hQ2 : Integrable (fun x => ‖Q x‖^2) μ := by rw [hQsq]; exact h2.indicator hS.compl
  have hYbound (x : Ω) : ‖Y x‖ ≤ R := by
    by_cases hx : x ∈ S
    · change ‖S.indicator X x‖ ≤ R
      rw [Set.indicator_of_mem hx]
      exact hx
    · simp only [Y, Set.indicator_of_notMem hx, norm_zero]
      exact hR
  have hmean : ‖∫ x, Y x ∂μ‖ ≤ R := by
    simpa only [probReal_univ, mul_one]
      using norm_integral_le_of_norm_le_const (μ := μ) (Filter.Eventually.of_forall hYbound)
  have hdecomp (x : Ω) : X x = Y x+Q x := by
    by_cases hx : x ∈ S <;> simp [Y, Q, hx]
  have hqm : (∫ x, Q x ∂μ) = -(∫ x, Y x ∂μ) := by
    have hh : (∫ x, X x ∂μ) = (∫ x, Y x ∂μ)+(∫ x, Q x ∂μ) := by
      calc
        _ = ∫ x, Y x+Q x ∂μ := integral_congr_ae (Filter.Eventually.of_forall hdecomp)
        _ = _ := integral_add hYi hQi
    rw [hm] at hh
    exact eq_neg_of_add_eq_zero_right hh.symm
  dsimp only
  refine ⟨hYi.sub (integrable_const _), integral_centered_eq_zero μ Y hYi, ?_, ?_, ?_⟩
  · intro x
    exact (norm_sub_le _ _).trans (by linarith [hYbound x])
  · apply (integral_centered_norm_sq_le μ Y hYi hY2).trans
    apply integral_mono hY2 h2
    intro x
    by_cases hx : x ∈ S
    · simp [Y, Set.indicator_of_mem hx]
    · simp only [Y, Set.indicator_of_notMem hx, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
      exact sq_nonneg _
  · have heq (x : Ω) : X x-(Y x-∫ y, Y y ∂μ) = Q x-∫ y, Q y ∂μ := by
      rw [hqm, hdecomp]
      abel
    change (∫ x, ‖X x-(Y x-∫ y, Y y ∂μ)‖^2 ∂μ) ≤ _
    simp_rw [heq]
    apply (integral_centered_norm_sq_le μ Q hQi hQ2).trans
    rw [hQsq, integral_indicator hS.compl]
    have hcompl : Sᶜ = {x | R < ‖X x‖} := by ext x; simp [S, not_le]
    rw [hcompl]

#print axioms squareExp_tail_secondMoment
#print axioms recentered_truncation_moments
end SpectralRadiusUpperTail
