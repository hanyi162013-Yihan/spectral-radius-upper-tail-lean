import SpectralRadiusUpperTail.RealGinibreDominantIntegrable
import SpectralRadiusUpperTail.RealGinibreCoreDecay
import SpectralRadiusUpperTail.ShortIntervalIntegralLower
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Set

/-- A short interval to the right of `r` supplies the matching lower
exponential rate for the dominant real one-point term. -/
theorem realGinibreDominantTailLower (n : ℕ) (hn : 3 ≤ n)
    (r δ : ℝ) (hr : 1 < r) (hδ : 0 < δ) :
    (δ/(n : ℝ))*realGinibreCoreDensity n (r+δ) ≤
      ∫ x : ℝ in Ioi r, realGinibreDominantDensity n x := by
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hnpos
  have htail := realGinibreDominantDensity_integrableOn n hn r hr
  have hinterval : IntegrableOn
      (fun x => realGinibreDominantDensity n x) (Ioc r (r+δ)) :=
    htail.mono_set (by intro x hx; exact hx.1)
  have hbound (x : ℝ) (hx : x ∈ Icc r (r+δ)) :
      realGinibreCoreDensity n (r+δ)/(n : ℝ) ≤
        realGinibreDominantDensity n x := by
    have hx1 : 1 < x := lt_of_lt_of_le hr hx.1
    have hcore := realGinibreCoreDensity_antitone n hnpos x (r+δ) hx1 hx.2
    have hdiv := div_le_div_of_nonneg_right hcore hnR.le
    exact hdiv.trans (realGinibreDominantDensity_bounds n hn x hx1.le).1
  have hshort := short_interval_integral_lower
    (fun x => realGinibreDominantDensity n x) r (r+δ)
    (realGinibreCoreDensity n (r+δ)/(n : ℝ))
    (by linarith) hinterval hbound
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi r)]
      (fun x => realGinibreDominantDensity n x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx1 : 1 ≤ x := by linarith [show r < x from hx]
    have hxpos : 0 < x := by linarith
    have hq := realGinibreCoreDensity_pos n hnpos x hxpos
    exact (div_nonneg hq.le hnR.le).trans
      (realGinibreDominantDensity_bounds n hn x hx1).1
  have hsubset : Ioc r (r+δ) ⊆ Ioi r := by
    intro x hx
    exact hx.1
  have hmono := setIntegral_mono_set htail hnonneg hsubset.eventuallyLE
  calc
    (δ/(n : ℝ))*realGinibreCoreDensity n (r+δ) =
        ((r+δ)-r)*(realGinibreCoreDensity n (r+δ)/(n : ℝ)) := by ring
    _ ≤ ∫ x : ℝ in Ioc r (r+δ), realGinibreDominantDensity n x := hshort
    _ ≤ ∫ x : ℝ in Ioi r, realGinibreDominantDensity n x := hmono

#print axioms realGinibreDominantTailLower
end SpectralRadiusUpperTail
