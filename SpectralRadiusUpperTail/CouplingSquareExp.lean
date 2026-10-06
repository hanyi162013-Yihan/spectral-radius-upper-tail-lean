import SpectralRadiusUpperTail.CenteredSquareExp

namespace SpectralRadiusUpperTail
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- Exponential-square control of both marginals controls their difference under
any coupling; no independence between the coordinates is needed. -/
theorem coupling_difference_squareExp (π : Measure (E × E)) (μ ν : Measure E)
    (hfst : π.map Prod.fst = μ) (hsnd : π.map Prod.snd = ν)
    (c A B : ℝ) (hc : 0 ≤ c)
    (hμ : Integrable (fun x : E => Real.exp (c*‖x‖^2)) μ)
    (hν : Integrable (fun x : E => Real.exp (c*‖x‖^2)) ν)
    (hA : (∫ x : E, Real.exp (c*‖x‖^2) ∂μ) ≤ A)
    (hB : (∫ x : E, Real.exp (c*‖x‖^2) ∂ν) ≤ B) :
    Integrable (fun z : E × E => Real.exp ((c/4)*‖z.1-z.2‖^2)) π ∧
      (∫ z : E × E, Real.exp ((c/4)*‖z.1-z.2‖^2) ∂π) ≤ (A+B)/2 := by
  have hleft : Integrable (fun z : E × E => Real.exp (c*‖z.1‖^2)) π := by
    apply (integrable_map_measure (μ := π) (g := fun x : E => Real.exp (c*‖x‖^2))
      (by fun_prop) measurable_fst.aemeasurable).mp
    rw [hfst]
    exact hμ
  have hright : Integrable (fun z : E × E => Real.exp (c*‖z.2‖^2)) π := by
    apply (integrable_map_measure (μ := π) (g := fun x : E => Real.exp (c*‖x‖^2))
      (by fun_prop) measurable_snd.aemeasurable).mp
    rw [hsnd]
    exact hν
  have hle : (∫ z : E × E, Real.exp (c*‖z.1‖^2) ∂π) ≤ A := by
    rw [← integral_map (μ := π) (f := fun x : E => Real.exp (c*‖x‖^2))
      measurable_fst.aemeasurable (by fun_prop), hfst]
    exact hA
  have hre : (∫ z : E × E, Real.exp (c*‖z.2‖^2) ∂π) ≤ B := by
    rw [← integral_map (μ := π) (f := fun x : E => Real.exp (c*‖x‖^2))
      measurable_snd.aemeasurable (by fun_prop), hsnd]
    exact hB
  have hb (z : E × E) : Real.exp ((c/4)*‖z.1-z.2‖^2) ≤
      (Real.exp (c*‖z.1‖^2)+Real.exp (c*‖z.2‖^2))/2 := by
    apply (Real.exp_le_exp.mpr ?_).trans (exp_half_sum_le (c*‖z.1‖^2) (c*‖z.2‖^2))
    have hh := mul_le_mul_of_nonneg_left (norm_sub_sq_le_twice z.1 z.2) (by positivity : 0 ≤ c/4)
    nlinarith
  have htop : Integrable (fun z : E × E =>
      (Real.exp (c*‖z.1‖^2)+Real.exp (c*‖z.2‖^2))/2) π :=
    (hleft.add hright).div_const 2
  have hi : Integrable (fun z : E × E => Real.exp ((c/4)*‖z.1-z.2‖^2)) π :=
    htop.mono_nonneg (by fun_prop)
      (Filter.Eventually.of_forall (fun _ => Real.exp_nonneg _))
      (Filter.Eventually.of_forall hb)
  refine ⟨hi, ?_⟩
  have hh := integral_mono hi htop hb
  rw [integral_div, integral_add hleft hright] at hh
  linarith

/-- The actual centered coupling error has a square-exponential moment controlled
solely by its two marginal square-exponential moments. -/
theorem coupling_centered_squareExp (π : Measure (E × E)) [IsProbabilityMeasure π]
    (μ ν : Measure E) (hfst : π.map Prod.fst = μ) (hsnd : π.map Prod.snd = ν)
    (c A B : ℝ) (hc : 0 < c)
    (hμ : Integrable (fun x : E => Real.exp (c*‖x‖^2)) μ)
    (hν : Integrable (fun x : E => Real.exp (c*‖x‖^2)) ν)
    (hA : (∫ x : E, Real.exp (c*‖x‖^2) ∂μ) ≤ A)
    (hB : (∫ x : E, Real.exp (c*‖x‖^2) ∂ν) ≤ B) :
    Integrable (fun z : E × E =>
      Real.exp ((c/8)*‖(z.1-z.2)-∫ w, w.1-w.2 ∂π‖^2)) π ∧
      (∫ z : E × E, Real.exp ((c/8)*‖(z.1-z.2)-∫ w, w.1-w.2 ∂π‖^2) ∂π)
        ≤ ((A+B)/2)^2 := by
  obtain ⟨hi, hb⟩ := coupling_difference_squareExp π μ ν hfst hsnd c A B hc.le hμ hν hA hB
  have hh := centered_squareExp π (fun z : E × E => z.1-z.2) (by fun_prop)
    (c/4) ((A+B)/2) (by positivity) hi hb
  have heq : c/4/2 = c/8 := by ring
  simpa only [heq] using hh

#print axioms coupling_difference_squareExp
#print axioms coupling_centered_squareExp
end SpectralRadiusUpperTail
