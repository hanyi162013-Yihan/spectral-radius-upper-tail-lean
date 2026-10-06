import SpectralRadiusUpperTail.OutlierFromIsotropic
import SpectralRadiusUpperTail.HolomorphicFixedPointUnique
import SpectralRadiusUpperTail.RealResolventConjugation

namespace SpectralRadiusUpperTail
open Metric Set
open scoped BigOperators Matrix Matrix.Norms.L2Operator
variable {n : ℕ}

lemma real_outlier_of_annulus_isotropic (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ)
    (hv : (∑ i, ‖v i‖^2) = 1) (b : ℝ) (d r L ε : ℝ)
    (hd : 0 < d) (hr : 0 < r) (hL : 0 ≤ L) (hε : 0 ≤ ε)
    (hbelow : r ≤ ‖(b : ℂ)‖-3*d) (habove : ‖(b : ℂ)‖+3*d ≤ L)
    (hsmall : ‖(b : ℂ)‖*L*ε ≤ d/8)
    (h : matrixAnnulusIsotropicControl (A.map Complex.ofRealHom)
      (fun i => (v i : ℂ)) (fun i => (v i : ℂ)) r L ε) :
    ∃ z : ℝ, (z : ℂ) ∈ closedBall (b : ℂ) d ∧
      (z : ℂ) ∈ spectrum ℂ (A.map Complex.ofRealHom+
        (b : ℂ) • Matrix.vecMulVec (fun i => (v i : ℂ)) (star (fun i => (v i : ℂ)))) := by
  let Ac := A.map Complex.ofRealHom
  let vc := fun i => (v i : ℂ)
  let bc := (b : ℂ)
  have hvc : (∑ i, ‖vc i‖^2) = 1 := by simpa only [vc,Complex.norm_real] using hv
  let f : ℂ → ℂ := fun z => bc*z*matrixCoefficient vc vc (resolvent Ac z)
  have hann : ∀ z ∈ ball bc (3*d), r ≤ ‖z‖ ∧ ‖z‖ ≤ L := by
    intro z hz
    have hh := disk_norm_bounds bc z (3*d) hz
    exact ⟨hbelow.trans hh.1.le,hh.2.le.trans habove⟩
  have hres : ∀ z ∈ ball bc (3*d), z ∈ resolventSet ℂ Ac := by
    intro z hz
    exact (h z (hann z hz).1 (hann z hz).2).1
  have hcoef := differentiableOn_resolvent_coefficient Ac vc vc hvc.le hvc.le (ball bc (3*d)) hres
  have hf : DifferentiableOn ℂ f (ball bc (3*d)) := by
    exact (differentiableOn_id.const_mul bc).mul hcoef
  have hunit := matrixCoefficient_unit_self vc hvc
  have hmap : MapsTo f (ball bc (3*d)) (closedBall bc (d/8)) := by
    intro z hz
    have hz0 : z ≠ 0 := norm_pos_iff.mp (hr.trans_le (hann z hz).1)
    have hs := (h z (hann z hz).1 (hann z hz).2).2
    rw [hunit,mul_one] at hs
    have hid : f z-bc = bc*z*(matrixCoefficient vc vc (resolvent Ac z)-z⁻¹) := by
      dsimp [f]
      have hi : bc*z*z⁻¹ = bc := by rw [mul_assoc,mul_inv_cancel₀ hz0,mul_one]
      rw [mul_sub,hi]
    change dist (f z) bc ≤ d/8
    rw [dist_eq_norm,hid,norm_mul,norm_mul]
    apply le_trans _ hsmall
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hann z hz).2 (norm_nonneg bc)) hs.le
      (norm_nonneg _) (mul_nonneg (norm_nonneg bc) hL)
  obtain ⟨z,hz,hfix⟩ := holomorphic_near_constant_real_fixedPoint f b d hd hf hmap
    (fun z => real_resolvent_fixedPoint_conjugate A v b z)
  have hzB := closed_disk_in_triple bc d hd hz
  have hz0 : (z : ℂ) ≠ 0 := norm_pos_iff.mp (hr.trans_le (hann z hzB).1)
  have heq : bc*matrixCoefficient vc vc (resolvent Ac (z : ℂ)) = 1 := by
    have hh : z*(bc*matrixCoefficient vc vc (resolvent Ac (z : ℂ))) = z*1 := by
      simpa only [f,mul_one,mul_assoc,mul_comm,mul_left_comm] using hfix
    exact mul_left_cancel₀ hz0 hh
  exact ⟨z,hz,rankOne_resolvent_mem_spectrum Ac vc bc z (hres z hzB) heq⟩

#print axioms real_outlier_of_annulus_isotropic
end SpectralRadiusUpperTail
