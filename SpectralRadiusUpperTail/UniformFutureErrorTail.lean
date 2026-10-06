import SpectralRadiusUpperTail.UniformFutureEntryTail
import SpectralRadiusUpperTail.CouplingSquareExp

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators ENNReal
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂]

/-- The actual centered one-entry coupling error has a uniform square-exponential
moment under the original entry hypotheses and the explicit local conditions. -/
theorem gaussianFuture_centered_squareExp (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (v : ℕ → 𝕂) (N : ℕ) (hX : MemLp (fun x : 𝕂 => x) 2 μ)
    (hm : (∫ x : 𝕂, x ∂μ) = 0) (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1)
    (hv : ∑ i : Fin N, ‖v i.val‖^2 ≤ 1) (a d : ℝ)
    (ha : 0 < a) (hd : 0 < d)
    (hexp : Integrable (fun x : 𝕂 => Real.exp (4*d*‖x‖^2)) μ)
    (s : 𝕂) (T : 𝕂 →L[ℝ] 𝕂) (u : ℝ) (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (hsmall : gaussianScoreConstant a
      (rowSquareExpExponent (4*d) (∫ x : 𝕂, Real.exp (4*d*‖x‖^2) ∂μ)) (Real.log 2)*
        ‖T‖*(1+‖s‖+‖T‖) ≤ d*u)
    (herror : u*(∫ x : 𝕂, (1+‖x‖^2)*(d*(‖x‖+‖x‖^2))*
      Real.exp (d*(‖x‖+‖x‖^2)) ∂μ) ≤ 1/2) :
    let W := futureWeight μ (fun i x => v i*x) (gaussianSoftWeight a) N
    let g := fun x => (W (s-T x)).toReal/(W s).toReal
    let Z := ∫ x, g x ∂μ
    let π := densityCoupling μ (fun x => ENNReal.ofReal (g x/Z))
    let M := ∫ x : 𝕂, Real.exp (4*d*‖x‖^2) ∂μ
    Integrable (fun z : 𝕂 × 𝕂 =>
      Real.exp ((d/8)*‖(z.1-z.2)-∫ w, w.1-w.2 ∂π‖^2)) π ∧
      (∫ z : 𝕂 × 𝕂, Real.exp ((d/8)*‖(z.1-z.2)-∫ w, w.1-w.2 ∂π‖^2) ∂π)
        ≤ ((2*Real.exp d*M+M)/2)^2 := by
  let W := futureWeight μ (fun i x => v i*x) (gaussianSoftWeight a) N
  let g := fun x => (W (s-T x)).toReal/(W s).toReal
  let Z := ∫ x, g x ∂μ
  let π := densityCoupling μ (fun x => ENNReal.ofReal (g x/Z))
  let ν := μ.withDensity (fun x => ENNReal.ofReal (g x/Z))
  have hcouple := gaussianFuture_likelihood_coupling μ v N hX hm hvar hv a d ha hd
    hexp s T u hu hu1 hsmall herror
  have hentry := gaussianFuture_conditional_squareExp μ v N hX hm hvar hv a d ha hd
    hexp s T u hu hu1 hsmall herror
  haveI : IsProbabilityMeasure π := hcouple.2.1
  have hb (x : 𝕂) : Real.exp (d*‖x‖^2) ≤ Real.exp (4*d*‖x‖^2) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hd.le (sq_nonneg ‖x‖)])
  have hμd : Integrable (fun x : 𝕂 => Real.exp (d*‖x‖^2)) μ :=
    hexp.mono_nonneg (by fun_prop)
      (Filter.Eventually.of_forall (fun _ => Real.exp_nonneg _))
      (Filter.Eventually.of_forall hb)
  exact coupling_centered_squareExp π ν μ hcouple.2.2.1 hcouple.2.2.2.1 d _ _ hd
    hentry.2.1 hμd hentry.2.2 (integral_mono hμd hexp hb)

#print axioms gaussianFuture_centered_squareExp
end SpectralRadiusUpperTail
