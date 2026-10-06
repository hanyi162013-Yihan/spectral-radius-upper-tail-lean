import SpectralRadiusUpperTail.ProductSumIntegration
import Mathlib.Tactic.Linarith

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- Actual finite-product replacement. Uniform one-coordinate errors add over
coordinates; Fubini and every intermediate integral are justified by boundedness. -/
theorem bounded_product_sum_replacement
    (f : E → ℝ) (hf : Measurable f) (B : ℝ) (hB : ∀ x, |f x| ≤ B)
    (N : ℕ) (μ ν : Fin N → Measure α)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)]
    (φ : Fin N → α → E) (hφ : ∀ i, Measurable (φ i)) (δ : Fin N → ℝ)
    (hrep : ∀ i s, |(∫ x, f (s+φ i x) ∂μ i)-(∫ x, f (s+φ i x) ∂ν i)| ≤ δ i)
    (s : E) :
    |(∫ x : Fin N → α, f (s+∑ i, φ i (x i)) ∂Measure.pi μ)-
      (∫ x : Fin N → α, f (s+∑ i, φ i (x i)) ∂Measure.pi ν)| ≤ ∑ i, δ i := by
  induction N generalizing s with
  | zero => simp
  | succ N ih =>
    let ψ := fun y : Fin N → α => ∑ i, φ i.succ (y i)
    have hψ : Measurable ψ := measurable_finite_sum _ (fun i => hφ i.succ)
    have hMM := bounded_shift_product_integrable (μ 0) (Measure.pi (fun i : Fin N => μ i.succ))
      f hf B hB (φ 0) ψ (hφ 0) hψ s
    have hMN := bounded_shift_product_integrable (μ 0) (Measure.pi (fun i : Fin N => ν i.succ))
      f hf B hB (φ 0) ψ (hφ 0) hψ s
    have hNN := bounded_shift_product_integrable (ν 0) (Measure.pi (fun i : Fin N => ν i.succ))
      f hf B hB (φ 0) ψ (hφ 0) hψ s
    have htail (x : α) :
        |(∫ y : Fin N → α, f (s+φ 0 x+ψ y) ∂Measure.pi (fun i : Fin N => μ i.succ))-
          (∫ y : Fin N → α, f (s+φ 0 x+ψ y) ∂Measure.pi (fun i : Fin N => ν i.succ))|
            ≤ ∑ i : Fin N, δ i.succ := by
      exact ih (fun i => μ i.succ) (fun i => ν i.succ)
        (fun i => φ i.succ) (fun i => hφ i.succ) (fun i => δ i.succ)
        (fun i t => hrep i.succ t) (s+φ 0 x)
    have hleft := integral_difference_of_pointwise (μ 0) _ _
      hMM.integral_prod_left hMN.integral_prod_left (∑ i : Fin N, δ i.succ) htail
    have hhead (y : Fin N → α) :
        |(∫ x : α, f (s+φ 0 x+ψ y) ∂μ 0)-(∫ x : α, f (s+φ 0 x+ψ y) ∂ν 0)| ≤ δ 0 := by
      simpa only [add_right_comm s (ψ y)] using hrep 0 (s+ψ y)
    have hright :
        |(∫ x : α, ∫ y : Fin N → α, f (s+φ 0 x+ψ y)
              ∂Measure.pi (fun i : Fin N => ν i.succ) ∂μ 0)-
          (∫ x : α, ∫ y : Fin N → α, f (s+φ 0 x+ψ y)
              ∂Measure.pi (fun i : Fin N => ν i.succ) ∂ν 0)| ≤ δ 0 := by
      rw [integral_integral_swap (f := fun x y => f (s+φ 0 x+ψ y)) hMN,
        integral_integral_swap (f := fun x y => f (s+φ 0 x+ψ y)) hNN]
      exact integral_difference_of_pointwise (Measure.pi (fun i : Fin N => ν i.succ)) _ _
        hMN.integral_prod_right hNN.integral_prod_right (δ 0) hhead
    rw [product_sum_integral_succ N μ φ hφ f hf B hB s,
      product_sum_integral_succ N ν φ hφ f hf B hB s, Fin.sum_univ_succ]
    have ht := abs_sub_le
      (∫ x : α, ∫ y : Fin N → α, f (s+φ 0 x+ψ y)
        ∂Measure.pi (fun i : Fin N => μ i.succ) ∂μ 0)
      (∫ x : α, ∫ y : Fin N → α, f (s+φ 0 x+ψ y)
        ∂Measure.pi (fun i : Fin N => ν i.succ) ∂μ 0)
      (∫ x : α, ∫ y : Fin N → α, f (s+φ 0 x+ψ y)
        ∂Measure.pi (fun i : Fin N => ν i.succ) ∂ν 0)
    change |(∫ x : α, ∫ y : Fin N → α, f (s+φ 0 x+ψ y)
      ∂Measure.pi (fun i : Fin N => μ i.succ) ∂μ 0)-
      (∫ x : α, ∫ y : Fin N → α, f (s+φ 0 x+ψ y)
      ∂Measure.pi (fun i : Fin N => ν i.succ) ∂ν 0)| ≤ _
    linarith

#print axioms bounded_product_sum_replacement
end SpectralRadiusUpperTail
