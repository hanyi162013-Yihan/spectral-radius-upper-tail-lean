import SpectralRadiusUpperTail.HolomorphicNearConstant
import SpectralRadiusUpperTail.OutlierDiskGeometry
import SpectralRadiusUpperTail.UnitVectorCoefficient
import SpectralRadiusUpperTail.ResolventCoefficientAnalytic
import SpectralRadiusUpperTail.RankOneResolventCriterion
import SpectralRadiusUpperTail.FiniteRightIsotropicProbability

namespace SpectralRadiusUpperTail
open Metric Set
open scoped BigOperators Matrix Matrix.Norms.L2Operator
variable {n : ℕ}

/-- Uniform isotropic control creates an actual rank-one outlier near b. -/
lemma outlier_of_annulus_isotropic (A : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ)
    (hv : (∑ i, ‖v i‖^2) = 1) (b : ℂ) (d r L ε : ℝ)
    (hd : 0 < d) (hr : 0 < r) (hL : 0 ≤ L) (hε : 0 ≤ ε)
    (hbelow : r ≤ ‖b‖-3*d) (habove : ‖b‖+3*d ≤ L)
    (hsmall : ‖b‖*L*ε ≤ d/8)
    (h : matrixAnnulusIsotropicControl A v v r L ε) :
    ∃ z ∈ closedBall b d, z ∈ spectrum ℂ (A+b • Matrix.vecMulVec v (star v)) := by
  let f : ℂ → ℂ := fun z => b*z*matrixCoefficient v v (resolvent A z)
  have hann : ∀ z ∈ ball b (3*d), r ≤ ‖z‖ ∧ ‖z‖ ≤ L := by
    intro z hz
    have hh := disk_norm_bounds b z (3*d) hz
    exact ⟨hbelow.trans hh.1.le,hh.2.le.trans habove⟩
  have hres : ∀ z ∈ ball b (3*d), z ∈ resolventSet ℂ A := by
    intro z hz
    exact (h z (hann z hz).1 (hann z hz).2).1
  have hcoef := differentiableOn_resolvent_coefficient A v v hv.le hv.le (ball b (3*d)) hres
  have hf : DifferentiableOn ℂ f (ball b (3*d)) := by
    exact (differentiableOn_id.const_mul b).mul hcoef
  have hunit := matrixCoefficient_unit_self v hv
  have hmap : MapsTo f (ball b (3*d)) (closedBall b (d/8)) := by
    intro z hz
    have hz0 : z ≠ 0 := norm_pos_iff.mp (hr.trans_le (hann z hz).1)
    have hs := (h z (hann z hz).1 (hann z hz).2).2
    rw [hunit,mul_one] at hs
    have hid : f z-b = b*z*(matrixCoefficient v v (resolvent A z)-z⁻¹) := by
      dsimp [f]
      have hi : b*z*z⁻¹ = b := by rw [mul_assoc,mul_inv_cancel₀ hz0,mul_one]
      rw [mul_sub,hi]
    change dist (f z) b ≤ d/8
    rw [dist_eq_norm,hid,norm_mul,norm_mul]
    apply le_trans _ hsmall
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hann z hz).2 (norm_nonneg b)) hs.le
      (norm_nonneg _) (mul_nonneg (norm_nonneg b) hL)
  obtain ⟨z,hz,hfix⟩ := holomorphic_near_constant_fixedPoint f b d hd hf hmap
  have hzB := closed_disk_in_triple b d hd hz
  have hz0 : z ≠ 0 := norm_pos_iff.mp (hr.trans_le (hann z hzB).1)
  have heq : b*matrixCoefficient v v (resolvent A z) = 1 := by
    have hh : z*(b*matrixCoefficient v v (resolvent A z)) = z*1 := by
      simpa only [f,mul_one,mul_assoc,mul_comm,mul_left_comm] using hfix
    exact mul_left_cancel₀ hz0 hh
  exact ⟨z,hz,rankOne_resolvent_mem_spectrum A v b z (hres z hzB) heq⟩

#print axioms outlier_of_annulus_isotropic
end SpectralRadiusUpperTail
