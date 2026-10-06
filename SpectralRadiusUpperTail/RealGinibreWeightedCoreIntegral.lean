import SpectralRadiusUpperTail.RealGinibreWeightedCorePointwise
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory

/-- Exact positive-half-line power integral of the dominant uncut real
Ginibre one-point factor. -/
theorem realGinibreCoreDensity_weighted_integral (n k : ℕ)
    (hn : 0 < n) :
    (∫ x in Set.Ioi (0 : ℝ), x^(2*k) * realGinibreCoreDensity n x) =
      (((n : ℝ)/2)^((n : ℝ)/2)/Real.Gamma ((n : ℝ)/2)) *
        (((n : ℝ)/2)^(-(((n : ℝ)+2*(k : ℝ))/2)) *
          (1/2)*Real.Gamma (((n : ℝ)+2*(k : ℝ))/2)) := by
  let b : ℝ := (n : ℝ)/2
  let q : ℝ := (n : ℝ)-1+2*(k : ℝ)
  let C : ℝ := b^((n : ℝ)/2)/Real.Gamma ((n : ℝ)/2)
  have hb : 0 < b := by dsimp [b]; positivity
  have hq : -1 < q := by
    dsimp [q]
    have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have hkR : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  calc
    _ = ∫ x in Set.Ioi (0 : ℝ),
        C * (x^q * Real.exp (-b*x^(2 : ℝ))) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact realGinibreCoreDensity_weighted_pointwise n k x hx
    _ = C * (∫ x in Set.Ioi (0 : ℝ),
        x^q * Real.exp (-b*x^(2 : ℝ))) := by rw [integral_const_mul]
    _ = C * (b^(-(q+1)/2) * (1/2) *
        Real.Gamma ((q+1)/2)) := by
      exact congrArg (fun t : ℝ => C*t)
        (integral_rpow_mul_exp_neg_mul_rpow
          (p := 2) (q := q) (b := b) (by norm_num) hq hb)
    _ = _ := by
      congr 1
      dsimp [b, q, C]
      congr 1
      · congr 1
        ring
      · congr 1
        ring

/-- The same exact integral in Gamma-ratio form. -/
theorem realGinibreCoreDensity_weighted_integral_ratio (n k : ℕ)
    (hn : 0 < n) :
    (∫ x in Set.Ioi (0 : ℝ), x^(2*k) * realGinibreCoreDensity n x) =
      (1/2)*((n : ℝ)/2)^(-(k : ℝ)) *
        (Real.Gamma ((n : ℝ)/2+(k : ℝ))/Real.Gamma ((n : ℝ)/2)) := by
  let b : ℝ := (n : ℝ)/2
  have hb : 0 < b := by dsimp [b]; positivity
  have hpow : b^((n : ℝ)/2)*b^(-(b+(k : ℝ))) =
      b^(-(k : ℝ)) := by
    rw [← Real.rpow_add hb]
    congr 1
    dsimp [b]
    ring
  rw [realGinibreCoreDensity_weighted_integral n k hn]
  have harg : (((n : ℝ)+2*(k : ℝ))/2) = b+(k : ℝ) := by
    dsimp [b]
    ring
  rw [harg]
  change (b^((n : ℝ)/2)/Real.Gamma b) *
    (b^(-(b+(k : ℝ))) * (1/2) *
      Real.Gamma (b+(k : ℝ))) =
      (1/2)*b^(-(k : ℝ)) *
        (Real.Gamma (b+(k : ℝ))/Real.Gamma b)
  calc
    _ = (1/2)*(b^((n : ℝ)/2)*b^(-(b+(k : ℝ)))) *
        (Real.Gamma (b+(k : ℝ))/Real.Gamma b) := by ring
    _ = _ := by rw [hpow]

#print axioms realGinibreCoreDensity_weighted_integral
#print axioms realGinibreCoreDensity_weighted_integral_ratio
end SpectralRadiusUpperTail
