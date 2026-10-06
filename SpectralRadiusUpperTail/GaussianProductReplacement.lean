import SpectralRadiusUpperTail.ScalarGaussianReplacement
import SpectralRadiusUpperTail.ProductReplacement

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂]

/-- A uniform cubic-coefficient replacement estimate for the actual iid product
Gaussian-soft normalizer in either scalar field. -/
theorem gaussian_product_replacement (μ ν : Measure 𝕂)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hXμ : MemLp (fun x : 𝕂 => x) 2 μ) (hXν : MemLp (fun x : 𝕂 => x) 2 ν)
    (hm : (∫ x : 𝕂, x ∂μ) = ∫ x : 𝕂, x ∂ν)
    (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = ∫ x : 𝕂, ‖x‖^2 ∂ν)
    (hpseudo : (∫ x : 𝕂, x^2 ∂μ) = ∫ x : 𝕂, x^2 ∂ν)
    (h3μ : Integrable (fun x : 𝕂 => ‖x‖^3) μ)
    (h3ν : Integrable (fun x : 𝕂 => ‖x‖^3) ν)
    (a : ℝ) (ha : 0 < a) (N : ℕ) (v : Fin N → 𝕂) (s : 𝕂) :
    |(∫ x : Fin N → 𝕂, Real.exp (-‖s-∑ i, v i*x i‖^2/a) ∂Measure.pi (fun _ => μ))-
      (∫ x : Fin N → 𝕂, Real.exp (-‖s-∑ i, v i*x i‖^2/a) ∂Measure.pi (fun _ => ν))| ≤
      ((gaussianThirdConstant a/2)*((∫ x : 𝕂, ‖x‖^3 ∂μ)+(∫ x : 𝕂, ‖x‖^3 ∂ν)))*
        ∑ i, ‖v i‖^3 := by
  let f := fun z : 𝕂 => Real.exp (-‖z‖^2/a)
  let C := (gaussianThirdConstant a/2)*((∫ x : 𝕂, ‖x‖^3 ∂μ)+(∫ x : 𝕂, ‖x‖^3 ∂ν))
  have hf : Measurable f := by fun_prop
  have hB (z : 𝕂) : |f z| ≤ 1 := by
    dsimp only [f]
    rw [abs_of_nonneg (Real.exp_nonneg _)]
    exact Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (sq_nonneg _)) ha.le)
  have hrep (i : Fin N) (t : 𝕂) :
      |(∫ x : 𝕂, f (t+(-v i)*x) ∂μ)-(∫ x : 𝕂, f (t+(-v i)*x) ∂ν)| ≤ C*‖v i‖^3 := by
    simpa only [f, C, norm_neg] using rclike_gaussian_scalar_replacement μ ν hXμ hXν
      hm hvar hpseudo h3μ h3ν a ha t (-v i)
  have hh := bounded_product_sum_replacement f hf 1 hB N (fun _ => μ) (fun _ => ν)
    (fun i x => (-v i)*x) (fun _ => by fun_prop) (fun i => C*‖v i‖^3) hrep s
  simpa only [f, neg_mul, Finset.sum_neg_distrib, ← sub_eq_add_neg, ← Finset.mul_sum] using hh

lemma coefficient_cube_sum_le {ι : Type*} [Fintype ι] (v : ι → 𝕂) (ε : ℝ)
    (hε : 0 ≤ ε) (hmax : ∀ i, ‖v i‖ ≤ ε) (henergy : ∑ i, ‖v i‖^2 ≤ 1) :
    ∑ i, ‖v i‖^3 ≤ ε := by
  calc
    _ ≤ ∑ i, ε*‖v i‖^2 := Finset.sum_le_sum (fun i _ => by
      have hh := mul_le_mul_of_nonneg_right (hmax i) (sq_nonneg ‖v i‖)
      nlinarith only [hh])
    _ = ε*(∑ i, ‖v i‖^2) := (Finset.mul_sum _ _ _).symm
    _ ≤ ε*1 := mul_le_mul_of_nonneg_left henergy hε
    _ = _ := mul_one _

/-- The product error is linear in the maximal coefficient when total coefficient
energy is at most one; this yields the flat-row O(n^(-1/2)) estimate. -/
theorem gaussian_product_replacement_flat (μ ν : Measure 𝕂)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hXμ : MemLp (fun x : 𝕂 => x) 2 μ) (hXν : MemLp (fun x : 𝕂 => x) 2 ν)
    (hm : (∫ x : 𝕂, x ∂μ) = ∫ x : 𝕂, x ∂ν)
    (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = ∫ x : 𝕂, ‖x‖^2 ∂ν)
    (hpseudo : (∫ x : 𝕂, x^2 ∂μ) = ∫ x : 𝕂, x^2 ∂ν)
    (h3μ : Integrable (fun x : 𝕂 => ‖x‖^3) μ)
    (h3ν : Integrable (fun x : 𝕂 => ‖x‖^3) ν)
    (a : ℝ) (ha : 0 < a) (N : ℕ) (v : Fin N → 𝕂) (s : 𝕂) (ε : ℝ)
    (hε : 0 ≤ ε) (hmax : ∀ i, ‖v i‖ ≤ ε) (henergy : ∑ i, ‖v i‖^2 ≤ 1) :
    |(∫ x : Fin N → 𝕂, Real.exp (-‖s-∑ i, v i*x i‖^2/a) ∂Measure.pi (fun _ => μ))-
      (∫ x : Fin N → 𝕂, Real.exp (-‖s-∑ i, v i*x i‖^2/a) ∂Measure.pi (fun _ => ν))| ≤
      ((gaussianThirdConstant a/2)*((∫ x : 𝕂, ‖x‖^3 ∂μ)+(∫ x : 𝕂, ‖x‖^3 ∂ν)))*ε := by
  apply (gaussian_product_replacement μ ν hXμ hXν hm hvar hpseudo h3μ h3ν a ha N v s).trans
  apply mul_le_mul_of_nonneg_left (coefficient_cube_sum_le v ε hε hmax henergy)
  exact mul_nonneg (div_nonneg (gaussianThirdConstant_nonneg a ha) (by norm_num))
    (add_nonneg (integral_nonneg (fun x => by positivity)) (integral_nonneg (fun x => by positivity)))

#print axioms gaussian_product_replacement
#print axioms gaussian_product_replacement_flat
end SpectralRadiusUpperTail
