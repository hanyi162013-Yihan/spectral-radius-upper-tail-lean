import SpectralRadiusUpperTail.RealGinibreWeightedCorePointwise
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory

/-- The weighted uncut real one-point factor is integrable on the positive
half-line; this supplies the integrability needed for density comparisons. -/
theorem realGinibreCoreDensity_weighted_integrableOn (n k : ℕ)
    (hn : 0 < n) :
    IntegrableOn (fun x : ℝ => x^(2*k)*realGinibreCoreDensity n x)
      (Set.Ioi 0) := by
  let b : ℝ := (n : ℝ)/2
  let q : ℝ := (n : ℝ)-1+2*(k : ℝ)
  let C : ℝ := b^((n : ℝ)/2)/Real.Gamma ((n : ℝ)/2)
  have hb : 0 < b := by dsimp [b]; positivity
  have hq : -1 < q := by
    dsimp [q]
    have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have hkR : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hbase : IntegrableOn
      (fun x : ℝ => x^q * Real.exp (-b*x^(2 : ℝ))) (Set.Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow hq (by norm_num) hb
  have hsource : IntegrableOn
      (fun x : ℝ => C*(x^q * Real.exp (-b*x^(2 : ℝ))))
      (Set.Ioi 0) := hbase.const_mul C
  apply hsource.congr_fun _ measurableSet_Ioi
  intro x hx
  exact (realGinibreCoreDensity_weighted_pointwise n k x hx).symm

#print axioms realGinibreCoreDensity_weighted_integrableOn
end SpectralRadiusUpperTail
