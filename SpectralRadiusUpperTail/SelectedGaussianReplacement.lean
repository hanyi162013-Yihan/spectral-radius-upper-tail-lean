import SpectralRadiusUpperTail.GaussianProductReplacement
import SpectralRadiusUpperTail.GaussianFiniteCalculus
import SpectralRadiusUpperTail.CoordinateSelectionLaw

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators

noncomputable def mixedCoordinateLaw {n : ℕ} (μ ν : Measure ℂ) (I : Finset (Fin n)) (j : Fin n) : Measure ℂ :=
  if j ∈ I then μ else ν

instance mixedCoordinateLaw_probability {n : ℕ} (μ ν : Measure ℂ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (I : Finset (Fin n)) (j : Fin n) :
    IsProbabilityMeasure (mixedCoordinateLaw μ ν I j) := by
  unfold mixedCoordinateLaw
  split_ifs <;> infer_instance

lemma gaussian_selected_replacement (μ ν : Measure ℂ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hXμ : MemLp (fun x : ℂ => x) 2 μ) (hXν : MemLp (fun x : ℂ => x) 2 ν)
    (hm : (∫ x : ℂ, x ∂μ) = ∫ x : ℂ, x ∂ν)
    (hv : (∫ x : ℂ, ‖x‖^2 ∂μ) = ∫ x : ℂ, ‖x‖^2 ∂ν)
    (hp : (∫ x : ℂ, x^2 ∂μ) = ∫ x : ℂ, x^2 ∂ν)
    (h3μ : Integrable (fun x : ℂ => ‖x‖^3) μ) (h3ν : Integrable (fun x : ℂ => ‖x‖^3) ν)
    (a : ℝ) (ha : 0 < a) (n : ℕ) (I : Finset (Fin n)) (v : Fin n → ℂ) (t : ℂ) :
    |gaussianFiniteNormalizer μ a v t-
      (∫ x : Fin n → ℂ, Real.exp (-‖t-∑ j, v j*x j‖^2/a) ∂Measure.pi (mixedCoordinateLaw μ ν I))| ≤
      ∑ j, if j ∈ I then 0 else
        ((gaussianThirdConstant a/2)*((∫ x : ℂ, ‖x‖^3 ∂μ)+(∫ x : ℂ, ‖x‖^3 ∂ν)))*‖v j‖^3 := by
  let f : ℂ → ℝ := fun z => Real.exp (-‖z‖^2/a)
  let C := (gaussianThirdConstant a/2)*((∫ x : ℂ, ‖x‖^3 ∂μ)+(∫ x : ℂ, ‖x‖^3 ∂ν))
  have hf : Measurable f := by dsimp [f]; fun_prop
  have hB (z : ℂ) : |f z| ≤ 1 := by
    dsimp [f]
    rw [abs_of_nonneg (Real.exp_nonneg _)]
    exact Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (by linarith [sq_nonneg ‖z‖]) ha.le)
  have hrep (j : Fin n) (s : ℂ) :
      |(∫ x : ℂ, f (s+(-v j)*x) ∂μ)-(∫ x : ℂ, f (s+(-v j)*x) ∂mixedCoordinateLaw μ ν I j)| ≤
        if j ∈ I then 0 else C*‖v j‖^3 := by
    by_cases hj : j ∈ I
    · simp [mixedCoordinateLaw, hj]
    · simpa only [mixedCoordinateLaw, hj, if_false, f, C, norm_neg] using
        rclike_gaussian_scalar_replacement μ ν hXμ hXν hm hv hp h3μ h3ν a ha s (-v j)
  have hh := bounded_product_sum_replacement f hf 1 hB n (fun _ => μ) (mixedCoordinateLaw μ ν I)
    (fun j x => (-v j)*x) (fun _ => by fun_prop) (fun j => if j ∈ I then 0 else C*‖v j‖^3) hrep t
  simpa only [gaussianFiniteNormalizer, f, C, neg_mul, Finset.sum_neg_distrib, ← sub_eq_add_neg] using hh

#print axioms mixedCoordinateLaw
#print axioms mixedCoordinateLaw_probability
#print axioms gaussian_selected_replacement
end SpectralRadiusUpperTail
