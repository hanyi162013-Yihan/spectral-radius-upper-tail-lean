import SpectralRadiusUpperTail.MarkedRealRankWeights
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Set
open scoped ENNReal Matrix Matrix.Norms.Operator

/-- The fixed oriented angular chart contains the identity direction. -/
theorem markedRealAngularPositiveSource_zero (m : ℕ) :
    (0 : RealSchurMixedOrbitIndex (markedRealTwoBlockSizes m) → ℝ) ∈
      markedRealAngularPositiveSource m := by
  constructor
  · exact realSchurMixedAngularProjectionChart_zero_mem_source
      (markedRealTwoBlockSizes m)
  · simp [realSchurMixedAngularFrame]

/-- Its angular Jacobian weight has strictly positive total mass.
This is local geometric nondegeneracy; its exact global sphere mass is
still a separate step. -/
theorem markedRealAngularWeight_lintegral_pos (m : ℕ) :
    0 < (∫⁻ ω : RealSchurMixedOrbitIndex
      (markedRealTwoBlockSizes m) → ℝ,
      markedRealAngularWeight m ω) := by
  classical
  let V : Set (RealSchurMixedOrbitIndex
      (markedRealTwoBlockSizes m) → ℝ) :=
    markedRealAngularPositiveSource m ∩
      {ω | 0 < realSchurMixedAngularJacobian
        (markedRealTwoBlockSizes m) ω}
  have hV : IsOpen V :=
    (isOpen_markedRealAngularPositiveSource m).inter
      (isOpen_Ioi.preimage (markedRealAngularJacobian_continuous m))
  have hzero : (0 : RealSchurMixedOrbitIndex
      (markedRealTwoBlockSizes m) → ℝ) ∈ V := by
    refine ⟨markedRealAngularPositiveSource_zero m, ?_⟩
    simp [realSchurMixedAngularJacobian_zero]
  have hpositive : 0 < (volume : Measure
      (RealSchurMixedOrbitIndex (markedRealTwoBlockSizes m) → ℝ)) V :=
    hV.measure_pos volume ⟨0,hzero⟩
  have hsub : V ⊆ Function.support (markedRealAngularWeight m) := by
    intro ω hω
    have hval : 0 < |realSchurMixedAngularJacobian
        (markedRealTwoBlockSizes m) ω| :=
      abs_pos.mpr (ne_of_gt hω.2)
    change markedRealAngularWeight m ω ≠ 0
    change (if ω ∈ markedRealAngularPositiveSource m then
      ENNReal.ofReal |realSchurMixedAngularJacobian
        (markedRealTwoBlockSizes m) ω| else 0) ≠ 0
    rw [if_pos hω.1]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr hval)
  exact (lintegral_pos_iff_support
    (markedRealAngularWeight_measurable m)).2
      (lt_of_lt_of_le hpositive (measure_mono hsub))

#print axioms markedRealAngularWeight_lintegral_pos
end SpectralRadiusUpperTail
