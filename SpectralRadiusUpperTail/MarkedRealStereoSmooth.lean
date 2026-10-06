import SpectralRadiusUpperTail.MarkedRealStereoFrame
import SpectralRadiusUpperTail.RealSchurMixedOutputRotation
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix BigOperators Matrix.Norms.Operator

theorem markedRealVectorCons_contDiff (m : ℕ) (a : ℝ) :
    ContDiff ℝ ⊤ (markedRealVectorCons m a) := by
  apply contDiff_pi.mpr
  intro i
  unfold markedRealVectorCons
  split_ifs <;> fun_prop

theorem markedRealStereoDenom_contDiff (m : ℕ) :
    ContDiff ℝ ⊤ (markedRealStereoDenom m) := by
  unfold markedRealStereoDenom dotProduct
  fun_prop

theorem markedRealStereoFrame_contDiff (m : ℕ) :
    ContDiff ℝ ⊤ (markedRealStereoFrame m) := by
  let ι := RealSchurMixedCoord (markedRealTwoBlockSizes m)
  have he : ContDiff ℝ ⊤ (fun u => realMatrixEntryEquiv ι (markedRealStereoFrame m u)) := by
    apply contDiff_pi.mpr
    intro p
    change ContDiff ℝ ⊤ (fun u => markedRealStereoFrame m u p.1 p.2)
    simp only [markedRealStereoFrame_apply]
    have hv := markedRealVectorCons_contDiff m 1
    have hd := markedRealStereoDenom_contDiff m
    have hi := (contDiff_pi.mp hv) p.1
    have hj := (contDiff_pi.mp hv) p.2
    exact ((contDiff_const.sub ((contDiff_const.div hd
      (fun u => (markedRealStereoDenom_pos m u).ne')).mul (hi.mul hj))).mul contDiff_const)
  exact ((realMatrixEntryEquiv ι).symm.toContinuousLinearEquiv.contDiff).comp he

theorem markedRealStereoFrame_differentiable (m : ℕ) :
    Differentiable ℝ (markedRealStereoFrame m) :=
  (markedRealStereoFrame_contDiff m).differentiable (by simp)

#print axioms markedRealVectorCons_contDiff
#print axioms markedRealStereoDenom_contDiff
#print axioms markedRealStereoFrame_contDiff
#print axioms markedRealStereoFrame_differentiable
end SpectralRadiusUpperTail
