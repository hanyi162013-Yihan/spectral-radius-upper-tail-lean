import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Set Metric

/-- Polar integration of any real radial function on an exterior region of
the complex plane. Integrability is not needed for this equality of the
Bochner integrals, which use the library's zero convention when necessary. -/
theorem planarRadialExteriorIntegral (g : ℝ → ℝ) (r : ℝ) (hr : 0 < r) :
    (∫ z : ℂ in {z | r < ‖z‖}, g ‖z‖) =
      2 * (volume : Measure ℂ).real (ball 0 1) *
        (∫ s : ℝ in Ioi r, s*g s) := by
  let f : ℝ → ℝ := (Ioi r).indicator g
  have hp := MeasureTheory.integral_fun_norm_addHaar
    (μ := (volume : Measure ℂ)) f
  have hleft : (∫ z : ℂ, f ‖z‖) =
      (∫ z : ℂ in {z | r < ‖z‖}, g ‖z‖) := by
    have hset : MeasurableSet {z : ℂ | r < ‖z‖} :=
      measurableSet_lt measurable_const measurable_norm
    have heq : (fun z : ℂ => f ‖z‖) =
        {z : ℂ | r < ‖z‖}.indicator (fun z => g ‖z‖) := by
      funext z
      by_cases hz : r < ‖z‖ <;> simp [f, Set.indicator, hz]
    rw [heq, integral_indicator hset]
  have hright :
      (∫ s : ℝ in Ioi 0, s ^ (Module.finrank ℝ ℂ-1) • f s) =
      (∫ s : ℝ in Ioi r, s*g s) := by
    simp only [Complex.finrank_real_complex, Nat.reduceSubDiff, pow_one,
      smul_eq_mul]
    have heq : (fun s : ℝ => s*f s) =
        (Ioi r).indicator (fun s => s*g s) := by
      funext s
      by_cases hs : r < s <;> simp [f, Set.indicator, hs]
    rw [heq, setIntegral_indicator measurableSet_Ioi]
    have hset : Ioi (0 : ℝ) ∩ Ioi r = Ioi r := by
      ext s
      constructor
      · exact fun h => h.2
      · exact fun h => ⟨lt_trans hr h, h⟩
    rw [hset]
  rw [hleft, hright] at hp
  simpa only [Complex.finrank_real_complex, Nat.cast_ofNat, nsmul_eq_mul,
    smul_eq_mul, mul_assoc] using hp

#print axioms planarRadialExteriorIntegral
end SpectralRadiusUpperTail
