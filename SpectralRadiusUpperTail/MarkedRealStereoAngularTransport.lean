import SpectralRadiusUpperTail.MarkedRealStereoSourceVolume
import Mathlib.MeasureTheory.Constructions.Pi

namespace SpectralRadiusUpperTail
open MeasureTheory Classical
open scoped ENNReal Matrix

theorem markedRealStereoAngularWeight_lintegral_reindex (m : ℕ) :
    (∫⁻ w, markedRealStereoAngularWeight m w) =
      ∫⁻ u : Fin m → ℝ in {u | u ⬝ᵥ u < 1},
        ENNReal.ofReal ((2/markedRealStereoDenom m u)^m) := by
  let R := MeasurableEquiv.piCongrLeft
    (fun _ : RealSchurMixedOrbitIndex (markedRealTwoBlockSizes m) => ℝ)
      (markedRealOrbitEquiv m)
  have hR : MeasurePreserving R volume volume :=
    volume_measurePreserving_piCongrLeft _ _
  have hparam (u : Fin m → ℝ) : markedRealStereoParameterCLM m (R u) = u := by
    funext i
    exact MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : RealSchurMixedOrbitIndex (markedRealTwoBlockSizes m) => ℝ)
      (markedRealOrbitEquiv m) u i
  rw [← hR.lintegral_comp (markedRealStereoAngularWeight_measurable m)]
  have hs : MeasurableSet {u : Fin m → ℝ | u ⬝ᵥ u < 1} :=
    (isOpen_lt (by unfold dotProduct; fun_prop) continuous_const).measurableSet
  rw [← lintegral_indicator hs]
  apply lintegral_congr
  intro u
  simp only [markedRealStereoAngularWeight, markedRealStereoSource,
    Set.mem_setOf_eq, markedRealStereoAngularJacobian_abs, hparam,
    Set.indicator, Set.mem_setOf_eq]

#print axioms markedRealStereoAngularWeight_lintegral_reindex
end SpectralRadiusUpperTail
