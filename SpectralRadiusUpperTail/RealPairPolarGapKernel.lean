import SpectralRadiusUpperTail.RealPairPositivePolarIntegral

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal

noncomputable def realPairPolarFromGap (v : ℝ × ℝ) : ℝ × ℝ :=
  (Real.sqrt (v.2+4*v.1)/2,Real.sqrt v.2/2)

theorem realPairPolarFromGap_forward (q r : ℝ) (hr : 0 < r) (hqr : r < q) :
    realPairPolarFromGap (q^2-r^2,4*r^2)=(q,r) := by
  have hq : 0 < q := lt_trans hr hqr
  unfold realPairPolarFromGap
  dsimp only
  rw [show 4*r^2+4*(q^2-r^2)=(2*q)^2 by ring,
    show 4*r^2=(2*r)^2 by ring,Real.sqrt_sq_eq_abs,Real.sqrt_sq_eq_abs,
    abs_of_pos (by positivity : 0 < 2*q),abs_of_pos (by positivity : 0 < 2*r)]
  apply Prod.ext <;> dsimp <;> ring

theorem realPair_positivePolar_kernel_lintegral (g : ℝ × ℝ → ℝ≥0∞) :
    (∫⁻ z in realSchurPositivePairDomain, ENNReal.ofReal z.2*g z) =
      ∫⁻ v in realSchurPairCoordinateDomain,
        ENNReal.ofReal ((8*Real.sqrt (v.2+4*v.1))⁻¹)*g (realPairPolarFromGap v) := by
  let F := fun v : ℝ × ℝ => g (realPairPolarFromGap v)
  calc
    _ = ∫⁻ z in realSchurPositivePairDomain,
        ENNReal.ofReal z.2*F (z.1^2-z.2^2,4*z.2^2) := by
      apply setLIntegral_congr_fun realSchurPositivePairDomain_isOpen.measurableSet
      intro z hz
      dsimp only [F]
      rw [realPairPolarFromGap_forward z.1 z.2 hz.1 hz.2]
    _ = _ := realPair_positivePolar_gap_lintegral F

/-- The inverse radial coordinates produce exactly the already checked
positive real Schur pair chart. -/
theorem realPairPolarFromGap_pair (v : ℝ × ℝ) :
    ((realPairPolarFromGap v).1+(realPairPolarFromGap v).2,
      (realPairPolarFromGap v).1-(realPairPolarFromGap v).2) =
        realSchurPairFromCoordinates v.1 v.2 := by
  apply Prod.ext <;> dsimp [realPairPolarFromGap,realSchurPairFromCoordinates] <;> ring

#print axioms realPairPolarFromGap_forward
#print axioms realPair_positivePolar_kernel_lintegral
#print axioms realPairPolarFromGap_pair
end SpectralRadiusUpperTail
