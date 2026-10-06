import SpectralRadiusUpperTail.RealGinibreCoreDensity
import SpectralRadiusUpperTail.RealGinibreGammaCutoff

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The second, exponentially dominant term of Edelman's real Ginibre
one-point intensity, expressed with a normalized incomplete Gamma factor.
Identification with the matrix eigenvalue process is a separate input. -/
noncomputable def realGinibreDominantDensity (n : ℕ) (r : ℝ) : ℝ :=
  realGinibreCoreDensity n r *
    (gammaMeasure (((n : ℝ)-1)/2) 1 (Set.Iic ((n : ℝ)*r^2/2))).toReal

/-- The cutoff changes the dominant one-point term by at most a factor `n`
outside the unit disk, hence cannot affect its speed-`n` exponent. -/
theorem realGinibreDominantDensity_bounds (n : ℕ) (hn : 3 ≤ n)
    (r : ℝ) (hr : 1 ≤ r) :
    realGinibreCoreDensity n r/(n : ℝ) ≤
      realGinibreDominantDensity n r ∧
    realGinibreDominantDensity n r ≤ realGinibreCoreDensity n r := by
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hnpos
  have hrpos : 0 < r := by linarith
  have hcore : 0 ≤ realGinibreCoreDensity n r :=
    (realGinibreCoreDensity_pos n hnpos r hrpos).le
  have ha : (0 : ℝ) < ((n : ℝ)-1)/2 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  let μ := gammaMeasure (((n : ℝ)-1)/2) 1
  haveI : IsProbabilityMeasure μ :=
    isProbabilityMeasure_gammaMeasure ha (by norm_num : (0 : ℝ) < 1)
  let E : Set ℝ := Set.Iic ((n : ℝ)*r^2/2)
  have hlow : 1/(n : ℝ) ≤ (μ E).toReal := by
    have h := ENNReal.toReal_mono (measure_ne_top μ E)
      (realGinibre_gamma_cutoff_lower n hn r hr)
    simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ 1/(n : ℝ))] using h
  have hupp : (μ E).toReal ≤ 1 := by
    have hm : μ E ≤ 1 := by
      calc
        μ E ≤ μ Set.univ := measure_mono (Set.subset_univ E)
        _ = 1 := measure_univ
    have h := ENNReal.toReal_mono (by norm_num : (1 : ℝ≥0∞) ≠ ∞)
      hm
    simpa using h
  constructor
  · change realGinibreCoreDensity n r/(n : ℝ) ≤
      realGinibreCoreDensity n r * (μ E).toReal
    calc
      _ = realGinibreCoreDensity n r*(1/(n : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlow hcore
  · change realGinibreCoreDensity n r * (μ E).toReal ≤ _
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hupp hcore

#print axioms realGinibreDominantDensity_bounds
end SpectralRadiusUpperTail
