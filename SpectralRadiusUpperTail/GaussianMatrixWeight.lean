import SpectralRadiusUpperTail.GaussianFiniteCalculus
import Mathlib.MeasureTheory.Integral.Pi

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂] {n : ℕ}

noncomputable def gaussianMatrixWeight (a : ℝ) (v t : Fin n → 𝕂)
    (x : Fin n → Fin n → 𝕂) : ℝ :=
  Real.exp (-(∑ i, ‖t i-∑ j, v j*x i j‖^2)/a)

lemma gaussianMatrixWeight_eq_product (a : ℝ) (v t : Fin n → 𝕂)
    (x : Fin n → Fin n → 𝕂) :
    gaussianMatrixWeight a v t x = ∏ i, Real.exp (-‖t i-∑ j, v j*x i j‖^2/a) := by
  rw [gaussianMatrixWeight]
  simp only [← Finset.sum_neg_distrib,Finset.sum_div,Real.exp_sum]

lemma gaussianMatrixWeight_integral (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (a : ℝ) (v t : Fin n → 𝕂) :
    (∫ x : Fin n → Fin n → 𝕂, gaussianMatrixWeight a v t x
      ∂Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))) =
      ∏ i, gaussianFiniteNormalizer μ a v (t i) := by
  simp_rw [gaussianMatrixWeight_eq_product]
  exact integral_fintype_prod_eq_prod
    (μ := fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))
    (fun i (x : Fin n → 𝕂) => Real.exp (-‖t i-∑ j, v j*x j‖^2/a))

lemma gaussianMatrixWeight_pos (a : ℝ) (v t : Fin n → 𝕂) (x : Fin n → Fin n → 𝕂) :
    0 < gaussianMatrixWeight a v t x := Real.exp_pos _

lemma gaussianMatrixWeight_le_one (a : ℝ) (ha : 0 < a) (v t : Fin n → 𝕂)
    (x : Fin n → Fin n → 𝕂) : gaussianMatrixWeight a v t x ≤ 1 := by
  apply Real.exp_le_one_iff.2
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (Finset.sum_nonneg (fun _ _ => sq_nonneg _))) ha.le

#print axioms gaussianMatrixWeight
#print axioms gaussianMatrixWeight_eq_product
#print axioms gaussianMatrixWeight_integral
#print axioms gaussianMatrixWeight_pos
#print axioms gaussianMatrixWeight_le_one
end SpectralRadiusUpperTail
