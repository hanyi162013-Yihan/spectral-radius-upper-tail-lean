import SpectralRadiusUpperTail.RegressionEnvelopeTail

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators

/-- A pointwise compact estimate and the actual tail integral bound the
whole second moment. All measurability and integrability are explicit. -/
lemma integral_sq_le_compact_add_tail {Ω E F : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedAddCommGroup F] [MeasurableSpace F] [BorelSpace F]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (r : Ω → E) (S : Ω → F)
    (hS : Measurable S) (hi : Integrable (fun x => ‖r x‖^2) ν)
    (R B : ℝ) (hcompact : ∀ x, ‖S x‖ ≤ R → ‖r x‖ ≤ B) :
    (∫ x, ‖r x‖^2 ∂ν) ≤ B^2+(∫ x in {x | R < ‖S x‖}, ‖r x‖^2 ∂ν) := by
  classical
  let T := {x | R < ‖S x‖}
  have hT : MeasurableSet T := measurableSet_lt measurable_const hS.norm
  have hb (x : Ω) : ‖r x‖^2 ≤ B^2+T.indicator (fun y => ‖r y‖^2) x := by
    by_cases hx : R < ‖S x‖
    · simp only [T, Set.indicator_apply, Set.mem_ofPred_eq, hx, if_true]
      nlinarith [sq_nonneg B]
    · have hh := hcompact x (le_of_not_gt hx)
      have hB : 0 ≤ B := (norm_nonneg _).trans hh
      simpa only [T, Set.indicator_apply, Set.mem_ofPred_eq, hx, if_false, add_zero] using
        (sq_le_sq₀ (norm_nonneg _) hB).mpr hh
  have hh := integral_mono hi ((integrable_const (B^2)).add (hi.indicator hT)) hb
  simp only [Pi.add_apply] at hh
  rw [integral_add (integrable_const _) (hi.indicator hT), integral_const,
    probReal_univ, one_smul, integral_indicator hT] at hh
  exact hh

/-- Finite summation of the compact bounds uses only coefficient energy. -/
theorem sum_integral_sq_le_compact_add_tail {Ω E F ι : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedAddCommGroup F] [MeasurableSpace F] [BorelSpace F]
    [Fintype ι] (ν : Measure Ω) [IsProbabilityMeasure ν] (r : ι → Ω → E) (S : ι → Ω → F)
    (hS : ∀ j, Measurable (S j)) (hi : ∀ j, Integrable (fun x => ‖r j x‖^2) ν)
    (b : ι → ℝ) (hb : ∑ j, (b j)^2 ≤ 1) (C δ R T : ℝ)
    (hcompact : ∀ j x, ‖S j x‖ ≤ R → ‖r j x‖ ≤ C*δ*b j)
    (htail : (∑ j, ∫ x in {x | R < ‖S j x‖}, ‖r j x‖^2 ∂ν) ≤ T) :
    (∫ x, ∑ j, ‖r j x‖^2 ∂ν) ≤ C^2*δ^2+T := by
  rw [integral_finsetSum _ (fun j _ => hi j)]
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) =>
    integral_sq_le_compact_add_tail ν (r j) (S j) (hS j) (hi j) R (C*δ*b j) (hcompact j))
  rw [Finset.sum_add_distrib] at hsum
  have hc : (∑ j, (C*δ*b j)^2) ≤ C^2*δ^2 := by
    calc
      _ = (C^2*δ^2)*(∑ j, (b j)^2) := by
        simp_rw [mul_pow]
        exact (Finset.mul_sum _ _ _).symm
      _ ≤ (C^2*δ^2)*1 := mul_le_mul_of_nonneg_left hb (by positivity)
      _ = _ := mul_one _
  exact hsum.trans (add_le_add hc htail)

#print axioms sum_integral_sq_le_compact_add_tail
end SpectralRadiusUpperTail
