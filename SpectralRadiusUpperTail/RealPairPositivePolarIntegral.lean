import SpectralRadiusUpperTail.RealPairCartesianVolume
import SpectralRadiusUpperTail.RealSchurPairLIntegral

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal

/-- On q > r > 0, pass from the polar radius and skew coordinate to
b=q+r, c=q-r. The absolute inverse Jacobian is one half. -/
theorem realPair_positivePolar_lintegral (g : ℝ × ℝ → ℝ≥0∞) :
    (∫⁻ z in realSchurPositivePairDomain, g z) =
      ∫⁻ p in realSchurPositivePairDomain,
        ENNReal.ofReal (1/2 : ℝ) * g ((p.1+p.2)/2,(p.1-p.2)/2) := by
  let K := (1/2 : ℝ) • realPairSumDifference
  have hK (p : ℝ × ℝ) : K p=((p.1+p.2)/2,(p.1-p.2)/2) := by
    simp [K,realPairSumDifference_apply,div_eq_mul_inv,mul_comm]
  have hdet : K.det= -(1/2 : ℝ) := by
    change LinearMap.det ((1/2 : ℝ) • realPairSumDifference.toLinearMap)=_
    rw [LinearMap.det_smul]
    simp only [Module.finrank_prod,Module.finrank_self]
    change (1/2 : ℝ)^2 * realPairSumDifference.det=_
    rw [realPairSumDifference_det]
    norm_num
  have hinj : Set.InjOn K realSchurPositivePairDomain := by
    intro z _ w _ h
    rw [hK,hK] at h
    have h₁ := congrArg Prod.fst h
    have h₂ := congrArg Prod.snd h
    apply Prod.ext <;> dsimp at * <;> linarith
  have himage : K '' realSchurPositivePairDomain=realSchurPositivePairDomain := by
    ext z
    constructor
    · rintro ⟨p,hp,rfl⟩
      change 0 < p.2 ∧ p.2 < p.1 at hp
      rw [hK]
      change 0 < (p.1-p.2)/2 ∧ (p.1-p.2)/2 < (p.1+p.2)/2
      constructor <;> linarith
    · intro hz
      change 0 < z.2 ∧ z.2 < z.1 at hz
      refine ⟨(z.1+z.2,z.1-z.2),?_,?_⟩
      · change 0 < z.1-z.2 ∧ z.1-z.2 < z.1+z.2
        constructor <;> linarith
      · rw [hK]
        apply Prod.ext <;> dsimp <;> ring
  have h := lintegral_image_eq_lintegral_abs_det_fderiv_mul
    (f := K) (f' := fun _ => K) volume realSchurPositivePairDomain_isOpen.measurableSet
    (fun _ _ => K.hasFDerivAt.hasFDerivWithinAt) hinj g
  rw [himage,hdet] at h
  simpa only [hK,show |-(1/2 : ℝ)|=1/2 by norm_num] using h

/-- The radial Jacobian and the pair-coordinate Jacobian leave the
inverse-square-root gap density, with all constants explicit. -/
theorem realPair_positivePolar_gap_lintegral (F : ℝ × ℝ → ℝ≥0∞) :
    (∫⁻ z in realSchurPositivePairDomain,
      ENNReal.ofReal z.2 * F (z.1^2-z.2^2,4*z.2^2)) =
      ∫⁻ v in realSchurPairCoordinateDomain,
        ENNReal.ofReal ((8*Real.sqrt (v.2+4*v.1))⁻¹) * F v := by
  rw [realPair_positivePolar_lintegral]
  have hp (p : ℝ × ℝ) (h : p ∈ realSchurPositivePairDomain) :
      ENNReal.ofReal (1/2 : ℝ) *
        (ENNReal.ofReal ((p.1-p.2)/2) *
          F (((p.1+p.2)/2)^2-((p.1-p.2)/2)^2,4*((p.1-p.2)/2)^2)) =
      ENNReal.ofReal ((p.1-p.2)/4)*F (realSchurPairCoordinates p.1 p.2) := by
    have hcoords : (((p.1+p.2)/2)^2-((p.1-p.2)/2)^2,4*((p.1-p.2)/2)^2) =
        realSchurPairCoordinates p.1 p.2 := by
      apply Prod.ext <;> dsimp [realSchurPairCoordinates] <;> ring
    rw [hcoords,← mul_assoc,← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/2)]
    congr 2
    ring
  calc
    _ = ∫⁻ p in realSchurPositivePairDomain,
        ENNReal.ofReal ((p.1-p.2)/4)*F (realSchurPairCoordinates p.1 p.2) := by
      apply setLIntegral_congr_fun realSchurPositivePairDomain_isOpen.measurableSet
      intro p h
      exact hp p h
    _ = _ := by
      rw [realSchurPair_inverse_density_lintegral]
      apply setLIntegral_congr_fun realSchurPairCoordinateDomain_isOpen.measurableSet
      intro v hv
      dsimp only
      have hv' : 0 < v.1 ∧ 0 < v.2 := hv
      rw [realSchur_pair_chart_forward v.1 v.2 hv'.1 hv'.2,← mul_assoc,
        ← ENNReal.ofReal_mul (by unfold realSchurPairInverseJacobian; positivity)]
      congr 2
      have hs : Real.sqrt v.2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hv'.2)
      have hu : Real.sqrt (v.2+4*v.1) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by linarith [hv'.1,hv'.2]))
      unfold realSchurPairInverseJacobian realSchurPairFromCoordinates
      dsimp only
      field_simp [hs,hu]
      <;> ring

#print axioms realPair_positivePolar_lintegral
#print axioms realPair_positivePolar_gap_lintegral
end SpectralRadiusUpperTail
