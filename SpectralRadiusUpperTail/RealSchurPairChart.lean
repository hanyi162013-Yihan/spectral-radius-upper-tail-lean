import SpectralRadiusUpperTail.RealSchurPairCoordinates
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

/-- Inverse algebraic coordinates on the positive real Schur pair chart:
`u=bc>0` and `s=(b-c)^2>0`, with `b>c>0`. -/
noncomputable def realSchurPairFromCoordinates (u s : ℝ) : ℝ × ℝ :=
  ((Real.sqrt (s+4*u)+Real.sqrt s)/2,
   (Real.sqrt (s+4*u)-Real.sqrt s)/2)

theorem realSchur_pair_chart_forward (u s : ℝ)
    (hu : 0 < u) (hs : 0 < s) :
    realSchurPairCoordinates
      (realSchurPairFromCoordinates u s).1
      (realSchurPairFromCoordinates u s).2 = (u,s) := by
  have hs0 : 0 ≤ s := le_of_lt hs
  have hsum0 : 0 ≤ s+4*u := by positivity
  have hsqrtS : (Real.sqrt s)^2 = s := Real.sq_sqrt hs0
  have hsqrtSum : (Real.sqrt (s+4*u))^2 = s+4*u :=
    Real.sq_sqrt hsum0
  apply Prod.ext
  · change ((Real.sqrt (s+4*u)+Real.sqrt s)/2)*
      ((Real.sqrt (s+4*u)-Real.sqrt s)/2) = u
    nlinarith
  · change (((Real.sqrt (s+4*u)+Real.sqrt s)/2)-
      ((Real.sqrt (s+4*u)-Real.sqrt s)/2))^2 = s
    nlinarith

theorem realSchur_pair_chart_pos (u s : ℝ)
    (hu : 0 < u) (hs : 0 < s) :
    0 < (realSchurPairFromCoordinates u s).2 ∧
      (realSchurPairFromCoordinates u s).2 <
        (realSchurPairFromCoordinates u s).1 := by
  have hs0 : 0 ≤ s := le_of_lt hs
  have hsum0 : 0 ≤ s+4*u := by positivity
  have hsqrtS0 : 0 ≤ Real.sqrt s := Real.sqrt_nonneg _
  have hsqrtSpos : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hsqrtSum0 : 0 ≤ Real.sqrt (s+4*u) := Real.sqrt_nonneg _
  have hsqrtS : (Real.sqrt s)^2 = s := Real.sq_sqrt hs0
  have hsqrtSum : (Real.sqrt (s+4*u))^2 = s+4*u :=
    Real.sq_sqrt hsum0
  have hlt : Real.sqrt s < Real.sqrt (s+4*u) := by
    nlinarith
  constructor <;> change _ < _ <;> dsimp [realSchurPairFromCoordinates] <;> linarith

theorem realSchur_pair_chart_backward (b c : ℝ)
    (hc : 0 < c) (hcb : c < b) :
    realSchurPairFromCoordinates
      (realSchurPairCoordinates b c).1
      (realSchurPairCoordinates b c).2 = (b,c) := by
  have hb : 0 < b := lt_trans hc hcb
  have hsum : 0 ≤ b+c := by linarith
  have hdiff : 0 ≤ b-c := by linarith
  have hsqrtSum :
      Real.sqrt ((realSchurPairCoordinates b c).2+
        4*(realSchurPairCoordinates b c).1) = b+c := by
    rw [← realSchur_pair_coordinates_sum_sq]
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hsum]
  have hsqrtDiff :
      Real.sqrt (realSchurPairCoordinates b c).2 = b-c := by
    change Real.sqrt ((b-c)^2) = b-c
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hdiff]
  simp only [realSchurPairFromCoordinates, hsqrtSum, hsqrtDiff]
  apply Prod.ext <;> dsimp <;> ring

#print axioms realSchur_pair_chart_forward
#print axioms realSchur_pair_chart_pos
#print axioms realSchur_pair_chart_backward
end SpectralRadiusUpperTail
