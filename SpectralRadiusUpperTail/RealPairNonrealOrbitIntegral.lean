import SpectralRadiusUpperTail.RealPairNonrealMask
import SpectralRadiusUpperTail.RealEvenSquareTailIntegral
import SpectralRadiusUpperTail.RealPairPositiveDomainFubini

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix

theorem realPairInvariant_nonreal_orbit_lintegral
    (g : ((Fin 2 × Fin 2) → ℝ) → ℝ≥0∞) (hg : Measurable g)
    (h : RealPairOrthogonalInvariant g) :
    (∫⁻ A in realPairNonrealEntrySet, g A) = ENNReal.ofReal (8*Real.pi) *
      (∫⁻ x : ℝ, ∫⁻ q : ℝ, ∫⁻ r in Set.Ioi (0 : ℝ),
        ENNReal.ofReal r *
          (if r^2 < q^2 then g (fun ij => realSchurBlock x (q+r) (q-r) ij.1 ij.2) else 0)) := by
  classical
  rw [← lintegral_indicator measurableSet_realPairNonrealEntrySet,
    realPairInvariant_orbit_lintegral _ (hg.indicator measurableSet_realPairNonrealEntrySet)
      (RealPairOrthogonalInvariant.nonreal_mask g h)]
  simp only [Set.indicator_apply,realPairNonrealEntrySet_block]

/-- The two skew orientations have equal mass on the nonreal locus. -/
theorem realPairInvariant_polar_two_sectors
    (g : ((Fin 2 × Fin 2) → ℝ) → ℝ≥0∞) (hg : Measurable g)
    (h : RealPairOrthogonalInvariant g) (x : ℝ) :
    (∫⁻ q : ℝ, ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r *
      (if r^2 < q^2 then g (fun ij => realSchurBlock x (q+r) (q-r) ij.1 ij.2) else 0)) =
      2 * ∫⁻ z in realSchurPositivePairDomain,
        ENNReal.ofReal z.2 * g (fun ij => realSchurBlock x (z.1+z.2) (z.1-z.2) ij.1 ij.2) := by
  classical
  let B := fun z : ℝ × ℝ => fun ij : Fin 2 × Fin 2 =>
    realSchurBlock x (z.1+z.2) (z.1-z.2) ij.1 ij.2
  have hB : Measurable B := by
    apply measurable_pi_lambda
    intro ij
    rcases ij with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;> simp only [B,realSchurBlock] <;> fun_prop
  let K := fun z : ℝ × ℝ => ENNReal.ofReal z.2 * realPairNonrealEntrySet.indicator g (B z)
  have hK : Measurable K := measurable_snd.ennreal_ofReal.mul
    ((hg.indicator measurableSet_realPairNonrealEntrySet).comp hB)
  have hKval (q r : ℝ) : K (q,r)=ENNReal.ofReal r *
      (if r^2 < q^2 then g (B (q,r)) else 0) := by
    dsimp only [K,B]
    simp only [Set.indicator_apply,realPairNonrealEntrySet_block]
  have hswap : (∫⁻ q : ℝ, ∫⁻ r in Set.Ioi (0 : ℝ), K (q,r)) =
      ∫⁻ r in Set.Ioi (0 : ℝ), ∫⁻ q : ℝ, K (q,r) :=
    lintegral_lintegral_swap hK.aemeasurable
  have hinner (r : ℝ) (hr : 0 < r) : (∫⁻ q : ℝ, K (q,r)) =
      2*(ENNReal.ofReal r * ∫⁻ q in Set.Ioi r, g (B (q,r))) := by
    simp_rw [hKval]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hs : MeasurableSet {q : ℝ | r^2 < q^2} := isOpen_lt continuous_const (by fun_prop) |>.measurableSet
    have htest : (∫⁻ q : ℝ, if r^2 < q^2 then g (B (q,r)) else 0) =
        ∫⁻ q in {q : ℝ | r^2 < q^2}, g (B (q,r)) := by
      simpa only [Set.indicator_apply,Set.mem_ofPred_eq] using
        lintegral_indicator hs (fun q => g (B (q,r)))
    rw [htest,real_even_square_tail_lintegral r hr.le (fun q => g (B (q,r)))
      (fun q => realPairInvariant_skew_neg g h x r q)]
    ac_rfl
  calc
    _ = ∫⁻ q : ℝ, ∫⁻ r in Set.Ioi (0 : ℝ), K (q,r) := by simp only [hKval,B]
    _ = ∫⁻ r in Set.Ioi (0 : ℝ), ∫⁻ q : ℝ, K (q,r) := hswap
    _ = ∫⁻ r in Set.Ioi (0 : ℝ), 2*(ENNReal.ofReal r * ∫⁻ q in Set.Ioi r, g (B (q,r))) := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro r hr
      exact hinner r hr
    _ = 2 * ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r * ∫⁻ q in Set.Ioi r, g (B (q,r)) :=
      lintegral_const_mul' 2 _ (by norm_num)
    _ = _ := by
      congr 1
      change (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r *
        ∫⁻ q in Set.Ioi r, g (B (q,r))) =
          ∫⁻ z in realSchurPositivePairDomain, ENNReal.ofReal z.2 * g (B z)
      rw [realPair_positiveDomain_lintegral
        (fun z => ENNReal.ofReal z.2 * g (B z))
        (measurable_snd.ennreal_ofReal.mul (hg.comp hB))]
      apply lintegral_congr
      intro r
      exact (lintegral_const_mul' (ENNReal.ofReal r) (fun q => g (B (q,r))) ENNReal.ofReal_ne_top).symm

/-- Complete nonreal matrix integral over one positive polar sector,
including both orientations and the entire angular mass. -/
theorem realPairInvariant_nonreal_positive_lintegral
    (g : ((Fin 2 × Fin 2) → ℝ) → ℝ≥0∞) (hg : Measurable g)
    (h : RealPairOrthogonalInvariant g) :
    (∫⁻ A in realPairNonrealEntrySet, g A) = ENNReal.ofReal (16*Real.pi) *
      (∫⁻ x : ℝ, ∫⁻ z in realSchurPositivePairDomain,
        ENNReal.ofReal z.2 * g (fun ij => realSchurBlock x (z.1+z.2) (z.1-z.2) ij.1 ij.2)) := by
  rw [realPairInvariant_nonreal_orbit_lintegral g hg h]
  simp_rw [realPairInvariant_polar_two_sectors g hg h]
  rw [lintegral_const_mul' 2 _ (by norm_num),← mul_assoc]
  congr 1
  rw [show (16*Real.pi : ℝ)=(8*Real.pi)*2 by ring,
    ENNReal.ofReal_mul' (by norm_num : (0 : ℝ) ≤ 2),ENNReal.ofReal_ofNat]

#print axioms realPairInvariant_nonreal_orbit_lintegral
#print axioms realPairInvariant_polar_two_sectors
#print axioms realPairInvariant_nonreal_positive_lintegral
end SpectralRadiusUpperTail
