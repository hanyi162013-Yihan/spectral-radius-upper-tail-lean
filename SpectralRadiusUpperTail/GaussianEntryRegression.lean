import SpectralRadiusUpperTail.GaussianEntryTaylor
import SpectralRadiusUpperTail.RatioStability

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂] {N : ℕ}

noncomputable def gaussianEntryTaylorConstant (a K c m₃ : ℝ) : ℝ :=
  (6/a)*(m₃/Real.exp (-(K^2+1)/a)+
    |c| *((2/a)*(1+a))/(Real.exp (-(K^2+1)/a))^2)

/-- The actual conditional mean agrees with the actual logarithmic score to
quadratic order in the current coefficient, uniformly on a compact target set. -/
theorem gaussianEntry_mean_score (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (hm : (∫ x : 𝕂, x ∂μ) = 0)
    (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1) (h3 : Integrable (fun x : 𝕂 => ‖x‖^3) μ)
    (c : ℝ) (hc : ∀ z : 𝕂, (∫ x : 𝕂, (inner ℝ z x)^2 ∂μ) = c*‖z‖^2)
    (a : ℝ) (ha : 0 < a) (v : Fin N → 𝕂) (b s w : 𝕂)
    (hv : ‖b‖^2+∑ i, ‖v i‖^2 ≤ 1) (K : ℝ) (hs : ‖s‖ ≤ K) :
    |inner ℝ w (∫ x : 𝕂, x ∂gaussianEntryLaw μ a v b s)+
      c*deriv (fun t : ℝ => Real.log (gaussianFiniteNormalizer μ a v (s+t • (b*w)))) 0| ≤
      gaussianEntryTaylorConstant a K c (∫ x : 𝕂, ‖x‖^3 ∂μ)*‖w‖*‖b‖^2 := by
  let J := Real.exp (-(K^2+1)/a)
  let Bₐ := (2/a)*(1+a)
  let C := 6/a
  let A := gaussianFiniteNormalizer μ a v s
  let B := gaussianEntryNormalizer μ a v b s
  let P := ∫ x : 𝕂, inner ℝ w x*gaussianFiniteNormalizer μ a v (s-b*x) ∂μ
  let L := gaussianEntryLinear μ a v b s
  let m₃ := ∫ x : 𝕂, ‖x‖^3 ∂μ
  have hJ : 0 < J := Real.exp_pos _
  have hv' : ∑ i, ‖v i‖^2 ≤ 1 := by nlinarith [sq_nonneg ‖b‖]
  have hb : ‖b‖ ≤ 1 := by
    have hq : 0 ≤ ∑ i, ‖v i‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    nlinarith [norm_nonneg b]
  have hA : J ≤ A := gaussianFiniteNormalizer_lower μ hX hm hvar a ha v hv' s K hs
  have hB : J ≤ B := gaussianEntryNormalizer_lower μ hX hm hvar a ha v b s hv K hs
  obtain ⟨hden, hnum⟩ := gaussianEntry_taylor_bounds μ hX hm hvar h3 c hc a ha v b s w
  have hnum' : |P-(-c*L w)| ≤ (C*‖b‖^2)*‖w‖*m₃ := by
    convert! hnum using 1 <;> congr 1 <;> ring
  have hq : |-c*L w| ≤ |c| *Bₐ*‖b‖*‖w‖ := by
    rw [abs_mul, abs_neg]
    calc
      _ ≤ |c| *(Bₐ*‖b‖*‖w‖) := mul_le_mul_of_nonneg_left
        (gaussianEntryLinear_bound μ a ha v b s w) (abs_nonneg c)
      _ = _ := by ring
  have hh := ratio_difference_bound P (-c*L w) B A J (C*‖b‖^2)
    ((C*‖b‖^2)*‖w‖*m₃) (|c| *Bₐ*‖b‖*‖w‖) hJ hB hA hden hnum' hq
  have hsimple : ((C*‖b‖^2)*‖w‖*m₃)/J+
      (|c| *Bₐ*‖b‖*‖w‖)*(C*‖b‖^2)/J^2 ≤
      gaussianEntryTaylorConstant a K c m₃*‖w‖*‖b‖^2 := by
    calc
      _ = (‖b‖^2*‖w‖)*(C*m₃/J+(|c| *Bₐ*C/J^2)*‖b‖) := by ring
      _ ≤ (‖b‖^2*‖w‖)*(C*m₃/J+|c| *Bₐ*C/J^2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply add_le_add le_rfl
        have hcoef : 0 ≤ |c| *Bₐ*C/J^2 := by dsimp [Bₐ, C, J]; positivity
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hb hcoef
      _ = _ := by unfold gaussianEntryTaylorConstant; dsimp [C, Bₐ, J]; ring
  rw [gaussianEntryLaw_mean_projection μ hX a ha v b s w (hJ.trans_le hB),
    gaussianFiniteNormalizer_log_deriv μ hX hm hvar a ha v hv',
    ← gaussianEntryLinear_apply μ a ha]
  convert! hh.trans hsimple using 1 <;> congr 1 <;> ring

#print axioms gaussianEntry_mean_score
end SpectralRadiusUpperTail
