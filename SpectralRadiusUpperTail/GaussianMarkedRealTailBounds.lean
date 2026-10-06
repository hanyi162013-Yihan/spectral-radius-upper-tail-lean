import SpectralRadiusUpperTail.GaussianMarkedRealDensityIntegrable
import SpectralRadiusUpperTail.RealGinibreCoreDecay
import SpectralRadiusUpperTail.RightTailIntegralComparison
import SpectralRadiusUpperTail.ShortIntervalIntegralLower
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Set

/-- The marked-eigenline candidate has an integrable exponential envelope
outside every fixed radius greater than one. -/
theorem gaussianMarkedRealDensity_tail_upper
    (n : ℕ) (hn : 0 < n) (r : ℝ) (hr : 1 < r) :
    (∫ x : ℝ in Ioi r, gaussianMarkedRealDensity n x) ≤
      realGinibreCoreDensity n r / (r-1/r) := by
  have hrpos : 0 < r := by linarith
  have hs : 0 < r-1/r := by
    have hsq : 1 < r^2 := by nlinarith
    apply sub_pos.mpr
    apply (div_lt_iff₀ hrpos).mpr
    nlinarith
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have ha : 0 < (n : ℝ)*(r-1/r) := mul_pos hnR hs
  have hcorepos := realGinibreCoreDensity_pos n hn r hrpos
  have hi := gaussianMarkedRealDensity_integrableOn n hn r hr
  have h := right_tail_integral_le_of_exp_envelope
    (gaussianMarkedRealDensity n) r
    ((n : ℝ)*realGinibreCoreDensity n r)
    ((n : ℝ)*(r-1/r)) ha hi (by
      intro x hx
      have hx1 : 1 ≤ x := by linarith
      have hxpos : 0 < x := by linarith
      have hqx := realGinibreCoreDensity_pos n hn x hxpos
      have hbound := (gaussianMarkedRealDensity_sandwich n hn x hx1).2
      have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hpoly : ((n : ℝ)+1)/2 ≤ (n : ℝ) := by linarith
      have hfirst : gaussianMarkedRealDensity n x ≤
          (n : ℝ)*realGinibreCoreDensity n x :=
        hbound.trans (mul_le_mul_of_nonneg_right hpoly hqx.le)
      have hdecay := realGinibreCoreDensity_decay n hn r x hr (le_of_lt hx)
      have hsecond := mul_le_mul_of_nonneg_left hdecay hnR.le
      calc
        gaussianMarkedRealDensity n x ≤
            (n : ℝ)*realGinibreCoreDensity n x := hfirst
        _ ≤ ((n : ℝ)*realGinibreCoreDensity n r) *
              Real.exp (-((n : ℝ)*(r-1/r))*(x-r)) := by
          simpa only [neg_mul, mul_assoc] using hsecond)
  have hratio : ((n : ℝ)*realGinibreCoreDensity n r) /
      ((n : ℝ)*(r-1/r)) =
      realGinibreCoreDensity n r / (r-1/r) := by
    field_simp [hnR.ne', ne_of_gt hs]
  simpa only [hratio] using h

/-- A short interval to the right of the target radius supplies the
matching lower bound without the exact incomplete-Gamma one-point term. -/
theorem gaussianMarkedRealDensity_tail_lower
    (n : ℕ) (hn : 0 < n) (r δ : ℝ) (hr : 1 < r) (hδ : 0 < δ) :
    δ * realGinibreCoreDensity n (r+δ) ≤
      ∫ x : ℝ in Ioi r, gaussianMarkedRealDensity n x := by
  have hi := gaussianMarkedRealDensity_integrableOn n hn r hr
  have hinterval : IntegrableOn (gaussianMarkedRealDensity n) (Ioc r (r+δ)) :=
    hi.mono_set (by intro x hx; exact hx.1)
  have hshort := short_interval_integral_lower
    (gaussianMarkedRealDensity n) r (r+δ)
    (realGinibreCoreDensity n (r+δ))
    (by linarith) hinterval (by
      intro x hx
      have hx1 : 1 < x := lt_of_lt_of_le hr hx.1
      exact (realGinibreCoreDensity_antitone n hn x (r+δ) hx1 hx.2).trans
        (gaussianMarkedRealDensity_sandwich n hn x hx1.le).1)
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi r)]
      gaussianMarkedRealDensity n := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx1 : 1 ≤ x := by linarith [show r < x from hx]
    have hxpos : 0 < x := by linarith
    exact (realGinibreCoreDensity_pos n hn x hxpos).le.trans
      (gaussianMarkedRealDensity_sandwich n hn x hx1).1
  have hsubset : Ioc r (r+δ) ⊆ Ioi r := by
    intro x hx
    exact hx.1
  have hmono := setIntegral_mono_set hi hnonneg hsubset.eventuallyLE
  calc
    δ * realGinibreCoreDensity n (r+δ) =
        ((r+δ)-r)*realGinibreCoreDensity n (r+δ) := by ring
    _ ≤ ∫ x : ℝ in Ioc r (r+δ), gaussianMarkedRealDensity n x := hshort
    _ ≤ ∫ x : ℝ in Ioi r, gaussianMarkedRealDensity n x := hmono

#print axioms gaussianMarkedRealDensity_tail_upper
#print axioms gaussianMarkedRealDensity_tail_lower
end SpectralRadiusUpperTail
