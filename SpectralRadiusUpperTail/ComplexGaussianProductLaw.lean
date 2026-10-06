import SpectralRadiusUpperTail.ComplexGaussianMoments
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators

lemma complex_stdGaussian_product_law (n : ℕ) :
    (Measure.pi (fun _ : Fin n => stdGaussian ℂ)).map (toLp 2) =
      stdGaussian (EuclideanSpace ℂ (Fin n)) := by
  apply Measure.ext_of_charFun
  ext t
  rw [charFun_pi,charFun_stdGaussian]
  simp_rw [charFun_stdGaussian]
  rw [← Complex.exp_sum]
  congr 1
  simp only [← Complex.ofReal_pow]
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Complex.ofReal_sum,Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_ofNat]
  rw [← Finset.sum_div,← Finset.sum_neg_distrib]

#print axioms complex_stdGaussian_product_law
end SpectralRadiusUpperTail
