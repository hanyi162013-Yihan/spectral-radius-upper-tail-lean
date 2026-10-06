import SpectralRadiusUpperTail.ExponentialTruncation

namespace SpectralRadiusUpperTail
open MeasureTheory

lemma regression_weight_exp_bound (c γ r : ℝ) (hc : 0 < c) (hγ : γ ≤ c/4) :
    (1+r^2)*Real.exp (γ*(1+r^2)) ≤
      (Real.exp γ*(1+4/c))*Real.exp ((c/2)*r^2) := by
  have hr : r^2 ≤ (4/c)*Real.exp ((c/4)*r^2) := by
    have hh := Real.add_one_le_exp ((c/4)*r^2)
    calc
      _ ≤ (4*Real.exp ((c/4)*r^2))/c := (le_div_iff₀ hc).mpr (by nlinarith only [hh])
      _ = _ := by ring
  have he1 : 1 ≤ Real.exp ((c/4)*r^2) := Real.one_le_exp_iff.mpr (by positivity)
  have hp : 1+r^2 ≤ (1+4/c)*Real.exp ((c/4)*r^2) := by
    have hh := add_le_add he1 hr
    nlinarith only [hh]
  have he : Real.exp (γ*(1+r^2)) ≤ Real.exp γ*Real.exp ((c/4)*r^2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right hγ (sq_nonneg r)
    nlinarith only [hh]
  calc
    _ ≤ ((1+4/c)*Real.exp ((c/4)*r^2))*(Real.exp γ*Real.exp ((c/4)*r^2)) :=
      mul_le_mul hp he (Real.exp_nonneg _) (by positivity)
    _ = (Real.exp γ*(1+4/c))*(Real.exp ((c/4)*r^2)*Real.exp ((c/4)*r^2)) := by ring
    _ = _ := by rw [← Real.exp_add]; congr 2 <;> ring

/-- A uniform square-exponential prefix moment controls the weighted tail
that occurs in the global squared regression envelope. -/
theorem regression_envelope_tail {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) (X : Ω → E) (hX : Measurable X)
    (c γ M R : ℝ) (hc : 0 < c) (hγ : γ ≤ c/4) (hR : 0 ≤ R)
    (he : Integrable (fun x => Real.exp (c*‖X x‖^2)) μ)
    (hM : (∫ x, Real.exp (c*‖X x‖^2) ∂μ) ≤ M) :
    Integrable (fun x => (1+‖X x‖^2)*Real.exp (γ*(1+‖X x‖^2))) μ ∧
      (∫ x in {x | R < ‖X x‖}, (1+‖X x‖^2)*Real.exp (γ*(1+‖X x‖^2)) ∂μ) ≤
        (Real.exp γ*(1+4/c))*Real.exp (-(c/2)*R^2)*M := by
  classical
  let f := fun x => (1+‖X x‖^2)*Real.exp (γ*(1+‖X x‖^2))
  let A := Real.exp γ*(1+4/c)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hb (x : Ω) : f x ≤ A*Real.exp ((c/2)*‖X x‖^2) :=
    regression_weight_exp_bound c γ ‖X x‖ hc hγ
  have hfi : Integrable f μ := (he.const_mul A).mono_nonneg (by dsimp [f]; fun_prop)
    (Filter.Eventually.of_forall (fun x => by dsimp [f]; positivity))
    (Filter.Eventually.of_forall (fun x => (hb x).trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg ‖X x‖])) hA)))
  have hset : MeasurableSet {x | R < ‖X x‖} := measurableSet_lt measurable_const hX.norm
  have ht (x : Ω) : {y | R < ‖X y‖}.indicator f x ≤
      (A*Real.exp (-(c/2)*R^2))*Real.exp (c*‖X x‖^2) := by
    by_cases hx : R < ‖X x‖
    · simp only [Set.indicator_apply, Set.mem_ofPred_eq, hx, if_true]
      calc
        _ ≤ A*Real.exp ((c/2)*‖X x‖^2) := hb x
        _ ≤ A*Real.exp (-(c/2)*R^2+c*‖X x‖^2) := by
          apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hA
          have hh : R^2 ≤ ‖X x‖^2 := (sq_le_sq₀ hR (norm_nonneg _)).mpr hx.le
          nlinarith
        _ = _ := by rw [Real.exp_add]; ring
    · simp only [Set.indicator_apply, Set.mem_ofPred_eq, hx, if_false]
      positivity
  refine ⟨hfi, ?_⟩
  have hh := integral_mono (hfi.indicator hset)
    (he.const_mul (A*Real.exp (-(c/2)*R^2))) ht
  rw [integral_indicator hset, integral_const_mul] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left hM (by positivity))

#print axioms regression_envelope_tail
end SpectralRadiusUpperTail
