import SpectralRadiusUpperTail.GaussianEntryFutureBridge
import SpectralRadiusUpperTail.UniformRowSquareExp
import SpectralRadiusUpperTail.DensityCost
import SpectralRadiusUpperTail.SquareExpPolynomialMoments

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators ENNReal
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂] {N : ℕ}

noncomputable def gaussianFiniteRowLaw (μ : Measure 𝕂) (a : ℝ)
    (v : Fin N → 𝕂) (t : 𝕂) : Measure (Fin N → 𝕂) :=
  (Measure.pi (fun _ : Fin N => μ)).withDensity (fun x => ENNReal.ofReal
    (Real.exp (-‖t-∑ i, v i*x i‖^2/a)/gaussianFiniteNormalizer μ a v t))

/-- This finite-index law is exactly the source row marginal of the existing
Gaussian-soft sequential coupling. -/
theorem gaussianFiniteRowLaw_eq_coupling_source (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (hm : (∫ x : 𝕂, x ∂μ) = 0)
    (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1)
    (v : ℕ → 𝕂) (N : ℕ) (hv : ∑ i : Fin N, ‖v i.val‖^2 ≤ 1)
    (a : ℝ) (ha : 0 < a) (t : 𝕂) :
    gaussianFiniteRowLaw μ a (fun i : Fin N => v i.val) t =
      (Measure.pi (fun _ : Fin N => μ)).withDensity
        (fun x => gaussianSoftWeight a (t-∑ i : Fin N, v i.val*x i)/gaussianRowNormalizer μ v a N t) := by
  have hA : 0 < gaussianFiniteNormalizer μ a (fun i : Fin N => v i.val) t :=
    (Real.exp_pos _).trans_le (gaussianFiniteNormalizer_lower μ hX hm hvar a ha _ hv t ‖t‖ le_rfl)
  have hZ : gaussianRowNormalizer μ v a N t =
      ENNReal.ofReal (gaussianFiniteNormalizer μ a (fun i : Fin N => v i.val) t) := by
    rw [gaussianRowNormalizer_eq_future μ v a ha]
    have hfin := ne_top_of_le_ne_top ENNReal.one_ne_top
      (futureWeight_le_one μ (fun i x => v i*x) (gaussianSoftWeight a)
        (gaussianSoftWeight_le_one a ha) N t)
    calc
      _ = ENNReal.ofReal ((futureWeight μ (fun i x => v i*x) (gaussianSoftWeight a) N t).toReal) :=
        (ENNReal.ofReal_toReal hfin).symm
      _ = _ := congrArg ENNReal.ofReal (gaussianFutureWeight_eq_finiteNormalizer μ v N a ha t)
  rw [hZ]
  unfold gaussianFiniteRowLaw
  congr 1
  funext x
  rw [ENNReal.ofReal_div_of_pos hA]
  rfl

/-- Every weighted prefix (represented by a coefficient mask) has a uniform
square-exponential moment under the actual tilted row law. -/
theorem gaussianFiniteRowLaw_shifted_sum_squareExp (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hm : (∫ x : 𝕂, x ∂μ) = 0) (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1)
    (τ : ℝ) (hτ : 0 < τ) (hexp : Integrable (fun x : 𝕂 => Real.exp (τ*‖x‖^2)) μ)
    (v w : Fin N → 𝕂) (hv : ∑ i, ‖v i‖^2 ≤ 1) (hw : ∑ i, ‖w i‖^2 ≤ 1)
    (a : ℝ) (ha : 0 < a) (t : 𝕂) (K : ℝ) (ht : ‖t‖ ≤ K) :
    let c := rowSquareExpExponent τ (∫ x : 𝕂, Real.exp (τ*‖x‖^2) ∂μ)
    0 < c ∧
      Integrable (fun x : Fin N → 𝕂 => Real.exp ((c/2)*‖t-∑ i, w i*x i‖^2))
        (gaussianFiniteRowLaw μ a v t) ∧
      (∫ x, Real.exp ((c/2)*‖t-∑ i, w i*x i‖^2) ∂gaussianFiniteRowLaw μ a v t) ≤
        2*Real.exp ((K^2+1)/a+c*K^2) := by
  let P := Measure.pi (fun _ : Fin N => μ)
  let c := rowSquareExpExponent τ (∫ x : 𝕂, Real.exp (τ*‖x‖^2) ∂μ)
  let U := fun x : Fin N → 𝕂 => ∑ i, w i*x i
  let f := fun x : Fin N → 𝕂 => Real.exp ((c/2)*‖t-U x‖^2)
  let k := fun x : Fin N → 𝕂 => Real.exp (-‖t-∑ i, v i*x i‖^2/a)/gaussianFiniteNormalizer μ a v t
  let L := Real.exp ((K^2+1)/a)
  have hX : MemLp (fun x : 𝕂 => x) 2 μ :=
    (memLp_two_iff_integrable_sq_norm (by fun_prop)).mpr
      (squareExp_norm_pow_integrable μ τ hτ hexp 2)
  obtain ⟨hc, hUi, hUb⟩ := iid_row_squareExp μ w (hX.integrable (by norm_num)) hm hw τ hτ hexp
  have hJ := gaussianFiniteNormalizer_lower μ hX hm hvar a ha v hv t K ht
  have hJp : 0 < Real.exp (-(K^2+1)/a) := Real.exp_pos _
  have hk (x : Fin N → 𝕂) : k x ≤ L := by
    have hex : Real.exp (-‖t-∑ i, v i*x i‖^2/a) ≤ 1 :=
      Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg ‖t-∑ i, v i*x i‖]) ha.le)
    calc
      _ ≤ 1/Real.exp (-(K^2+1)/a) := div_le_div₀ (by norm_num : (0 : ℝ) ≤ 1) hex hJp hJ
      _ = L := by dsimp [L]; rw [neg_div, Real.exp_neg]; simp
  have hK : 0 ≤ K := (norm_nonneg t).trans ht
  have ht2 : ‖t‖^2 ≤ K^2 := (sq_le_sq₀ (norm_nonneg _) hK).mpr ht
  have hb (x : Fin N → 𝕂) : f x ≤ Real.exp (c*K^2)*Real.exp (c*‖U x‖^2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hn := norm_sub_sq_le_twice t (U x)
    have hs := mul_le_mul_of_nonneg_left hn (show 0 ≤ c/2 from by dsimp [c]; positivity)
    have hkt := mul_le_mul_of_nonneg_left ht2 hc.le
    nlinarith only [hs, hkt]
  have hUm : Measurable U := Finset.measurable_sum _
    (fun i _ => measurable_const.mul (measurable_pi_apply i))
  have hfm : Measurable f := Real.measurable_exp.comp
    (measurable_const.mul ((measurable_const.sub hUm).norm.pow_const 2))
  have hfi : Integrable f P := (hUi.const_mul (Real.exp (c*K^2))).mono_nonneg
    hfm.aestronglyMeasurable (Filter.Eventually.of_forall (fun _ => Real.exp_nonneg _))
    (Filter.Eventually.of_forall hb)
  have hfb : (∫ x, f x ∂P) ≤ 2*Real.exp (c*K^2) := by
    have hh := integral_mono hfi (hUi.const_mul (Real.exp (c*K^2))) hb
    rw [integral_const_mul] at hh
    exact hh.trans (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hUb (Real.exp_nonneg _))
  refine ⟨hc, boundedDensity_integrable P k f L hk hfi, ?_⟩
  have hh := boundedDensity_integral_le P k f L (Real.exp_nonneg _) hk hfi (fun _ => Real.exp_nonneg _)
  calc
    _ ≤ L*(∫ x, f x ∂P) := hh
    _ ≤ L*(2*Real.exp (c*K^2)) := mul_le_mul_of_nonneg_left hfb (Real.exp_nonneg _)
    _ = _ := by dsimp [L]; rw [Real.exp_add]; ring

#print axioms gaussianFiniteRowLaw_eq_coupling_source
#print axioms gaussianFiniteRowLaw_shifted_sum_squareExp
end SpectralRadiusUpperTail
