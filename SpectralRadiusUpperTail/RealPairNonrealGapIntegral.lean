import SpectralRadiusUpperTail.RealPairNonrealOrbitIntegral
import SpectralRadiusUpperTail.RealPairPolarGapKernel

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix

noncomputable def realPairGapBlockEntries (x : ℝ) (v : ℝ × ℝ) : (Fin 2 × Fin 2) → ℝ :=
  fun ij => realSchurBlock x (realSchurPairFromCoordinates v.1 v.2).1
    (realSchurPairFromCoordinates v.1 v.2).2 ij.1 ij.2

/-- Complete four-entry change of variables on the nonreal locus,
for every nonnegative orthogonally invariant observable. The variables
are the real part x, imaginary part squared u, and squared gap s.
Both skew orientations and the full angle contribute the factor 2*pi. -/
theorem realPairInvariant_nonreal_gap_lintegral
    (g : ((Fin 2 × Fin 2) → ℝ) → ℝ≥0∞) (hg : Measurable g)
    (h : RealPairOrthogonalInvariant g) :
    (∫⁻ A in realPairNonrealEntrySet, g A) = ENNReal.ofReal (2*Real.pi) *
      (∫⁻ x : ℝ, ∫⁻ v in realSchurPairCoordinateDomain,
        ENNReal.ofReal ((Real.sqrt (v.2+4*v.1))⁻¹) * g (realPairGapBlockEntries x v)) := by
  rw [realPairInvariant_nonreal_positive_lintegral g hg h]
  have hx (x : ℝ) :
      (∫⁻ z in realSchurPositivePairDomain,
        ENNReal.ofReal z.2 * g (fun ij => realSchurBlock x (z.1+z.2) (z.1-z.2) ij.1 ij.2)) =
      ∫⁻ v in realSchurPairCoordinateDomain,
        ENNReal.ofReal ((8*Real.sqrt (v.2+4*v.1))⁻¹) * g (realPairGapBlockEntries x v) := by
    rw [realPair_positivePolar_kernel_lintegral]
    apply lintegral_congr
    intro v
    congr 1
    exact congrArg (fun p : ℝ × ℝ => g (fun ij => realSchurBlock x p.1 p.2 ij.1 ij.2))
      (realPairPolarFromGap_pair v)
  simp_rw [hx]
  have hw (v : ℝ × ℝ) : ENNReal.ofReal ((8*Real.sqrt (v.2+4*v.1))⁻¹) =
      ENNReal.ofReal (1/8 : ℝ) * ENNReal.ofReal ((Real.sqrt (v.2+4*v.1))⁻¹) := by
    rw [show (8*Real.sqrt (v.2+4*v.1))⁻¹ = (1/8 : ℝ)*(Real.sqrt (v.2+4*v.1))⁻¹ by
      simp only [mul_inv_rev,one_div]; ring,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/8)]
  simp_rw [hw,mul_assoc,lintegral_const_mul' (ENNReal.ofReal (1/8 : ℝ)) _ ENNReal.ofReal_ne_top]
  rw [← mul_assoc,← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 16*Real.pi),
    show (16*Real.pi : ℝ)*(1/8)=2*Real.pi by ring]

#print axioms realPairInvariant_nonreal_gap_lintegral
end SpectralRadiusUpperTail
