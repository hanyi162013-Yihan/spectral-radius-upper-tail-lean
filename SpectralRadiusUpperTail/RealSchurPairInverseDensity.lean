import SpectralRadiusUpperTail.RealSchurPairChangeVariables
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory

/-- Reciprocal Jacobian of `(b,c) ↦ (u=bc,s=(b-c)^2)` on its positive chart. -/
noncomputable def realSchurPairInverseJacobian (u s : ℝ) : ℝ :=
  (2*Real.sqrt s*Real.sqrt (s+4*u))⁻¹

theorem realSchurPairInverseJacobian_cancel (b c : ℝ)
    (hc : 0 < c) (hcb : c < b) :
    2*(b-c)*(b+c)*
      realSchurPairInverseJacobian
        (realSchurPairCoordinates b c).1
        (realSchurPairCoordinates b c).2 = 1 := by
  have hdiff : 0 < b-c := sub_pos.mpr hcb
  have hsum : 0 < b+c := by linarith
  have hsqrtDiff :
      Real.sqrt (realSchurPairCoordinates b c).2 = b-c := by
    change Real.sqrt ((b-c)^2) = b-c
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hdiff]
  have hsqrtSum :
      Real.sqrt ((realSchurPairCoordinates b c).2+
        4*(realSchurPairCoordinates b c).1) = b+c := by
    rw [← realSchur_pair_coordinates_sum_sq]
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hsum]
  unfold realSchurPairInverseJacobian
  rw [hsqrtDiff, hsqrtSum]
  field_simp

/-- Pulling Lebesgue integration back to the `(u,s)` chart gives its exact
two-dimensional density. This is still only the internal coordinates of a
single real Schur pair block. -/
theorem realSchurPair_inverse_density_integral (g : ℝ × ℝ → ℝ) :
    (∫ p in realSchurPositivePairDomain, g p) =
      ∫ q in realSchurPairCoordinateDomain,
        g (realSchurPairFromCoordinates q.1 q.2) *
          realSchurPairInverseJacobian q.1 q.2 := by
  let H : ℝ × ℝ → ℝ := fun q =>
    g (realSchurPairFromCoordinates q.1 q.2) *
      realSchurPairInverseJacobian q.1 q.2
  have hcov := realSchurPair_chart_integral_explicit H
  calc
    (∫ p in realSchurPositivePairDomain, g p) =
        ∫ p in realSchurPositivePairDomain,
          2*(p.1-p.2)*(p.1+p.2)*
            H (realSchurPairCoordinates p.1 p.2) := by
      apply setIntegral_congr_fun realSchurPositivePairDomain_isOpen.measurableSet
      intro p hp
      change 0 < p.2 ∧ p.2 < p.1 at hp
      have hback := realSchur_pair_chart_backward p.1 p.2 hp.1 hp.2
      have hcancel := realSchurPairInverseJacobian_cancel p.1 p.2 hp.1 hp.2
      simp only [H, hback]
      change g p = 2*(p.1-p.2)*(p.1+p.2)*
        (g p * realSchurPairInverseJacobian
          (realSchurPairCoordinates p.1 p.2).1
          (realSchurPairCoordinates p.1 p.2).2)
      calc
        g p = g p * 1 := by ring
        _ = g p * (2*(p.1-p.2)*(p.1+p.2)*
            realSchurPairInverseJacobian
              (realSchurPairCoordinates p.1 p.2).1
              (realSchurPairCoordinates p.1 p.2).2) := by rw [hcancel]
        _ = _ := by ring
    _ = ∫ q in realSchurPairCoordinateDomain, H q := hcov.symm
    _ = _ := rfl

#print axioms realSchurPairInverseJacobian_cancel
#print axioms realSchurPair_inverse_density_integral
end SpectralRadiusUpperTail
