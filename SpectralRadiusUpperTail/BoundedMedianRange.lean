import SpectralRadiusUpperTail.BoundedCenterMean

namespace SpectralRadiusUpperTail
open MeasureTheory

/-- Both closed half-lines carry at least half the mass. -/
def IsProbabilityMedian {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (m : ℝ) : Prop :=
  1/2 ≤ μ.real {x | f x ≤ m} ∧ 1/2 ≤ μ.real {x | m ≤ f x}

lemma median_mem_bounded_range {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (m a R : ℝ)
    (hm : IsProbabilityMedian μ f m) (hR : ∀ᵐ x ∂μ, |f x-a| ≤ R) :
    |m-a| ≤ R := by
  apply abs_le.mpr
  constructor
  · by_contra hnot
    have hlt : m < a-R := by linarith
    have hz : μ {x | f x ≤ m} = 0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [hR] with x hx
      have hh := (abs_le.mp hx).1
      change ¬f x ≤ m
      linarith
    have hp := hm.1
    simp only [Measure.real, hz, ENNReal.toReal_zero] at hp
    norm_num at hp
  · by_contra hnot
    have hlt : a+R < m := by linarith
    have hz : μ {x | m ≤ f x} = 0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [hR] with x hx
      have hh := (abs_le.mp hx).2
      change ¬m ≤ f x
      linarith
    have hp := hm.2
    simp only [Measure.real, hz, ENNReal.toReal_zero] at hp
    norm_num at hp

lemma bounded_distance_to_median {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (m a R : ℝ)
    (hm : IsProbabilityMedian μ f m) (hR : ∀ᵐ x ∂μ, |f x-a| ≤ R) :
    ∀ᵐ x ∂μ, |f x-m| ≤ 2*R := by
  have hmed := median_mem_bounded_range μ f m a R hm hR
  filter_upwards [hR] with x hx
  have hh : |f x-m| ≤ |f x-a|+|m-a| := by
    calc
      _ = |(f x-a)-(m-a)| := by congr 1; ring
      _ ≤ _ := by simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (f x-a) 0 (m-a)
  linarith

#print axioms median_mem_bounded_range
#print axioms bounded_distance_to_median
end SpectralRadiusUpperTail
