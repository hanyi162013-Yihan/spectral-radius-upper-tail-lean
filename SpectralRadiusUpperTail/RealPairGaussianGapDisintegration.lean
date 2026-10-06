import SpectralRadiusUpperTail.RealPairGaussianGapIntegral
import SpectralRadiusUpperTail.SchurGapKernelLIntegral

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix

theorem realPairGapBlockEntries_measurable (x : ℝ) :
    Measurable (realPairGapBlockEntries x) := by
  apply measurable_pi_lambda
  intro ij
  rcases ij with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    simp only [realPairGapBlockEntries,realSchurBlock,realSchurPairFromCoordinates] <;> fun_prop

theorem realPair_coordinateDomain_lintegral
    (f : ℝ × ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ v in realSchurPairCoordinateDomain, f v) =
      ∫⁻ u in Set.Ioi (0 : ℝ), ∫⁻ s in Set.Ioi (0 : ℝ), f (u,s) := by
  change (∫⁻ v in Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ), f v
    ∂(volume : Measure ℝ).prod volume) = _
  exact setLIntegral_prod f hf.aemeasurable

/-- Exact disintegration of the four-entry Gaussian integral on the
nonreal locus into the real part, squared imaginary part, and the
normalized squared-gap probability law. -/
theorem realPairGaussian_nonreal_gap_disintegration
    (n : ℝ) (hn : 0 < n)
    (H : ((Fin 2 × Fin 2) → ℝ) → ℝ≥0∞) (hH : Measurable H)
    (hInv : RealPairOrthogonalInvariant H) :
    (∫⁻ A in realPairNonrealEntrySet, realPairGaussianWeight n A * H A) =
      ENNReal.ofReal (2*Real.pi) *
        (∫⁻ x : ℝ, ∫⁻ u in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (Real.exp (-n*(x^2+u))) *
            (((ENNReal.ofReal (n/2))⁻¹ * schurGapKernelNormalizer n (Real.sqrt u)) *
              ∫⁻ s, H (realPairGapBlockEntries x (u,s))
                ∂schurSquaredGapLaw n (Real.sqrt u))) := by
  rw [realPairGaussian_nonreal_gap_lintegral n H hH hInv]
  congr 1
  apply lintegral_congr
  intro x
  let f := fun v : ℝ × ℝ =>
    ENNReal.ofReal (Real.exp (-n*(x^2+v.1))) *
      (ENNReal.ofReal ((Real.sqrt (v.2+4*v.1))⁻¹) *
        ENNReal.ofReal (Real.exp (-(n/2)*v.2)) * H (realPairGapBlockEntries x v))
  have hf : Measurable f := by
    apply Measurable.mul
    · fun_prop
    · apply Measurable.mul
      · fun_prop
      · exact hH.comp (realPairGapBlockEntries_measurable x)
  change (∫⁻ v in realSchurPairCoordinateDomain, f v) = _
  rw [realPair_coordinateDomain_lintegral f hf]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro u hu
  dsimp only [f]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  have hroot : (Real.sqrt u)^2=u := Real.sq_sqrt hu.le
  have hg : Measurable (fun s : ℝ => H (realPairGapBlockEntries x (u,s))) :=
    (hH.comp (realPairGapBlockEntries_measurable x)).comp
      (measurable_const.prodMk measurable_id)
  have hh := schurGap_raw_lintegral_eq_normalized n (Real.sqrt u) hn
    (Real.sqrt_pos.mpr hu) (fun s => H (realPairGapBlockEntries x (u,s))) hg
  rw [hroot] at hh
  convert hh using 1
  apply lintegral_congr
  intro s
  ac_rfl

#print axioms realPairGapBlockEntries_measurable
#print axioms realPair_coordinateDomain_lintegral
#print axioms realPairGaussian_nonreal_gap_disintegration
end SpectralRadiusUpperTail
