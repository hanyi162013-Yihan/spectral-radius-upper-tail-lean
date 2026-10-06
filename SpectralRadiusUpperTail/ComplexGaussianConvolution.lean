import SpectralRadiusUpperTail.RealGaussianConvolution
import SpectralRadiusUpperTail.ComplexGaussianMoments
import Mathlib.MeasureTheory.Integral.Pi

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

lemma realGaussian_scaled_soft_convolution (c a : ℝ) (ha : 0 < a) (s : ℝ) :
    (∫ x : ℝ, Real.exp (-(s-c*x)^2/a) ∂gaussianReal 0 1) =
      Real.sqrt (a/(a+2*c^2))*Real.exp (-s^2/(a+2*c^2)) := by
  have hh := integral_map (μ := gaussianReal 0 1) (φ := fun x : ℝ => c*x)
    (f := fun x : ℝ => Real.exp (-(s-x)^2/a)) (by fun_prop) (by fun_prop)
  rw [gaussianReal_map_const_mul, mul_zero, mul_one, realGaussian_soft_convolution _ a ha] at hh
  simpa only [NNReal.coe_mk] using hh.symm

/-- A two-coordinate product calculation for the actual standard Gaussian on
the complex plane, using its real orthonormal basis. -/
theorem stdGaussian_complex_soft_convolution (c a : ℝ) (ha : 0 < a) (s : ℂ) :
    (∫ x : ℂ, Real.exp (-‖s-(c : ℂ)*x‖^2/a) ∂stdGaussian ℂ) =
      (a/(a+2*c^2))*Real.exp (-‖s‖^2/(a+2*c^2)) := by
  have hb (x : Fin 2 → ℝ) :
      (∑ i, x i • Complex.orthonormalBasisOneI i) = (x 0 : ℂ)+(x 1 : ℂ)*Complex.I := by
    simp [Fin.sum_univ_two, Complex.coe_orthonormalBasisOneI, Algebra.smul_def]
  have hf (x : Fin 2 → ℝ) :
      Real.exp (-‖s-(c : ℂ)*((x 0 : ℂ)+(x 1 : ℂ)*Complex.I)‖^2/a) =
        ∏ i : Fin 2, Real.exp (-((![s.re, s.im] : Fin 2 → ℝ) i-c*x i)^2/a) := by
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, ← Real.exp_add]
    congr 1
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply]
    ring
  have hm : Measurable (fun x : Fin 2 → ℝ => ∑ i, x i • Complex.orthonormalBasisOneI i) :=
    Finset.measurable_sum _ (fun _ _ => by fun_prop)
  rw [stdGaussian_eq_map_pi_orthonormalBasis Complex.orthonormalBasisOneI,
    integral_map hm.aemeasurable (by fun_prop)]
  simp_rw [hb, hf]
  rw [integral_fintype_prod_eq_prod
    (fun (i : Fin 2) (x : ℝ) => Real.exp (-((![s.re, s.im] : Fin 2 → ℝ) i-c*x)^2/a))]
  simp_rw [realGaussian_scaled_soft_convolution c a ha]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [mul_mul_mul_comm, ← pow_two,
    Real.sq_sqrt (div_nonneg ha.le (by positivity)), ← Real.exp_add]
  congr 1
  rw [← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply]
  ring

/-- Proper complex Gaussian convolution with arbitrary nonnegative total energy. -/
theorem properComplexGaussian_soft_convolution (q a : ℝ) (hq : 0 ≤ q) (ha : 0 < a) (s : ℂ) :
    (∫ x : ℂ, Real.exp (-‖s-x‖^2/a)
      ∂scalarPushforward properComplexGaussian ((Real.sqrt q : ℝ) : ℂ)) =
      (a/(a+q))*Real.exp (-‖s‖^2/(a+q)) := by
  rw [scalarPushforward, integral_map (by fun_prop) (by fun_prop),
    properComplexGaussian, scalarPushforward, integral_map (by fun_prop) (by fun_prop)]
  have he (x : ℂ) : (Real.sqrt q : ℂ)*(((Real.sqrt 2)⁻¹ : ℝ)*x) =
      ((Real.sqrt q*(Real.sqrt 2)⁻¹ : ℝ) : ℂ)*x := by
    push_cast
    ring
  simp_rw [he]
  rw [stdGaussian_complex_soft_convolution _ a ha]
  have hc : 2*(Real.sqrt q*(Real.sqrt 2)⁻¹)^2 = q := by
    rw [mul_pow, Real.sq_sqrt hq, inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  rw [hc]

#print axioms stdGaussian_complex_soft_convolution
#print axioms properComplexGaussian_soft_convolution
end SpectralRadiusUpperTail
