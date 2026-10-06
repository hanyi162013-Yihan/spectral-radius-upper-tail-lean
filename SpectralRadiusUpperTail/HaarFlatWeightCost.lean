import SpectralRadiusUpperTail.RealHaarFlatCost
import SpectralRadiusUpperTail.ComplexHaarFlatCost
import SpectralRadiusUpperTail.FlatHaarWeightBound
import SpectralRadiusUpperTail.InverseMassLogBound

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology ENNReal

lemma real_flatHaar_weight_cost (ε : ℝ) (hε : 0 < ε) :
    ∃ (L : ℝ) (hL : 1 ≤ L), ∀ᶠ n : ℕ in atTop,
      ∀ (a b : ℝ) (x : Fin n → Fin n → ℝ),
        flatSpectralMatrixWeight (haarFlatPrior ℝ n L hL) a b x ≤
          ENNReal.ofReal (Real.exp ((n : ℝ)*ε))*fullSpectralSphereWeight n a b x := by
  obtain ⟨L,hL,hcost⟩ := real_haar_flat_cost ε hε
  refine ⟨L,hL,?_⟩
  filter_upwards [hcost,eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hnpos : 0 < n := by omega
  letI := haarDirectionLaw_probability ℝ n hnpos
  rw [← haarDirectionLaw_flat_mass ℝ n L] at hn
  have hm : (haarDirectionLaw ℝ n) (flatUnitDirections ℝ n L) ≠ 0 := by
    intro hz
    simpa only [Measure.real,hz,ENNReal.toReal_zero,lt_self_iff_false] using hn.1
  have hb := inverse_mass_le_exp_of_log_lower _ (measure_ne_top _ _) hn.1 n hnpos ε hn.2
  intro a b x
  exact (flatHaar_matrixWeight_le_full n L hL hnpos hm a b x).trans (mul_le_mul' hb le_rfl)

lemma complex_flatHaar_weight_cost (ε : ℝ) (hε : 0 < ε) :
    ∃ (L : ℝ) (hL : 1 ≤ L), ∀ᶠ n : ℕ in atTop,
      ∀ (a : ℝ) (b : ℂ) (x : Fin n → Fin n → ℂ),
        flatSpectralMatrixWeight (haarFlatPrior ℂ n L hL) a b x ≤
          ENNReal.ofReal (Real.exp ((n : ℝ)*ε))*fullSpectralSphereWeight n a b x := by
  obtain ⟨L,hL,hcost⟩ := complex_haar_flat_cost ε hε
  refine ⟨L,hL,?_⟩
  filter_upwards [hcost,eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hnpos : 0 < n := by omega
  letI := haarDirectionLaw_probability ℂ n hnpos
  rw [← haarDirectionLaw_flat_mass ℂ n L] at hn
  have hm : (haarDirectionLaw ℂ n) (flatUnitDirections ℂ n L) ≠ 0 := by
    intro hz
    simpa only [Measure.real,hz,ENNReal.toReal_zero,lt_self_iff_false] using hn.1
  have hb := inverse_mass_le_exp_of_log_lower _ (measure_ne_top _ _) hn.1 n hnpos ε hn.2
  intro a b x
  exact (flatHaar_matrixWeight_le_full n L hL hnpos hm a b x).trans (mul_le_mul' hb le_rfl)

#print axioms real_flatHaar_weight_cost
#print axioms complex_flatHaar_weight_cost
end SpectralRadiusUpperTail
