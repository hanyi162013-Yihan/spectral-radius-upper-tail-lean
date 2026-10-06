import SpectralRadiusUpperTail.GammaCDFMarkov
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The incomplete Gamma factor in the real Ginibre one-point density is
at least `1/n` for every spectral location outside the unit disk. -/
theorem realGinibre_gamma_cutoff_lower (n : ℕ) (hn : 3 ≤ n)
    (r : ℝ) (hr : 1 ≤ r) :
    ENNReal.ofReal (1/(n : ℝ)) ≤
      gammaMeasure (((n : ℝ)-1)/2) 1 (Set.Iic ((n : ℝ)*r^2/2)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have ha : (0 : ℝ) < ((n : ℝ)-1)/2 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hb : (0 : ℝ) < (n : ℝ)/2 := by positivity
  have hmark := gamma_unit_cdf_markov_lower (((n : ℝ)-1)/2) ((n : ℝ)/2) ha hb
  have hquot : 0 ≤ (((n : ℝ)-1)/2)/((n : ℝ)/2) := by positivity
  have he : (1 : ℝ≥0∞) -
      ENNReal.ofReal (((n : ℝ)-1)/2) / ENNReal.ofReal ((n : ℝ)/2) =
      ENNReal.ofReal (1/(n : ℝ)) := by
    rw [← ENNReal.ofReal_div_of_pos hb]
    have hone : (1 : ℝ≥0∞) = ENNReal.ofReal 1 := by norm_num
    rw [hone]
    rw [← ENNReal.ofReal_sub 1 hquot]
    congr 1
    field_simp
    ring
  rw [he] at hmark
  have hr2 : (1 : ℝ) ≤ r^2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hr2 hnR.le
  have hbb : (n : ℝ)/2 ≤ (n : ℝ)*r^2/2 := by
    nlinarith
  exact hmark.trans (measure_mono (Set.Iic_subset_Iic.mpr hbb))

#print axioms realGinibre_gamma_cutoff_lower
end SpectralRadiusUpperTail
