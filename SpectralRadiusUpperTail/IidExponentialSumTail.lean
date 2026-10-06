import SpectralRadiusUpperTail.PositiveWeightNormalizer
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Moments.Basic
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped BigOperators

lemma iid_exponential_sum_tail {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (f : E → ℝ) (θ a : ℝ)
    (hθ : 0 < θ) (hi : Integrable (fun x => Real.exp (θ*f x)) μ)
    (hlog : Real.log (∫ x, Real.exp (θ*f x) ∂μ) ≤ θ*a/2) (N : ℕ) :
    (Measure.pi (fun _ : Fin N => μ)).real {x | (N : ℝ)*a ≤ ∑ i, f (x i)} ≤
      Real.exp (-θ*a*(N : ℝ)/2) := by
  have he (x : Fin N → E) : Real.exp (θ*∑ i, f (x i)) = ∏ i, Real.exp (θ*f (x i)) := by
    rw [Finset.mul_sum,Real.exp_sum]
  have hit : Integrable (fun x : Fin N → E => Real.exp (θ*∑ i, f (x i)))
      (Measure.pi (fun _ : Fin N => μ)) := by
    simp_rw [he]
    exact Integrable.fintype_prod (fun _ => hi)
  have hc := measure_ge_le_exp_mul_mgf (μ := Measure.pi (fun _ : Fin N => μ))
    (X := fun x : Fin N → E => ∑ i, f (x i)) ((N : ℝ)*a) hθ.le hit
  unfold mgf at hc
  simp_rw [he] at hc
  rw [integral_fintype_prod_eq_prod (μ := fun _ : Fin N => μ)
    (fun (_ : Fin N) (x : E) => Real.exp (θ*f x))] at hc
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hc
  have hm : 0 < ∫ x, Real.exp (θ*f x) ∂μ := integral_exp_pos hi
  have hb : (∫ x, Real.exp (θ*f x) ∂μ)^N ≤ Real.exp ((N : ℝ)*(θ*a/2)) := by
    rw [← Real.exp_log (pow_pos hm N),Real.log_pow]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg N))
  apply hc.trans
  calc
    _ ≤ Real.exp (-θ*((N : ℝ)*a))*Real.exp ((N : ℝ)*(θ*a/2)) :=
      mul_le_mul_of_nonneg_left hb (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

#print axioms iid_exponential_sum_tail
end SpectralRadiusUpperTail
