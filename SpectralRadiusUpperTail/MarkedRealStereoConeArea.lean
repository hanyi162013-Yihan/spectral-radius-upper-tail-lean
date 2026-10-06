import SpectralRadiusUpperTail.MarkedRealStereoConeCoverage
import SpectralRadiusUpperTail.MarkedRealStereoConeJacobian
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Group.Measure

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix BigOperators Matrix.Norms.Operator

theorem isOpen_markedRealStereoConeSource (m : ℕ) :
    IsOpen (markedRealStereoConeSource m) := by
  apply isOpen_Ioi.prod
  exact isOpen_lt (by unfold dotProduct; fun_prop) continuous_const

theorem markedRealStereoCone_lintegral_image (m : ℕ)
    (g : (ℝ × (Fin m → ℝ)) → ℝ≥0∞) :
    (∫⁻ y in {y | 0 < y.1}, g y) =
      ∫⁻ x in markedRealStereoConeSource m,
        ENNReal.ofReal (x.1^m * (2/markedRealStereoDenom m x.2)^m) *
          g (markedRealStereoConeMap m x) := by
  letI : Measure.IsAddHaarMeasure (volume : Measure (ℝ × (Fin m → ℝ))) := by
    change Measure.IsAddHaarMeasure ((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ)))
    infer_instance
  rw [← markedRealStereoConeMap_image m]
  have hh := lintegral_image_eq_lintegral_abs_det_fderiv_mul
    (volume : Measure (ℝ × (Fin m → ℝ)))
    (isOpen_markedRealStereoConeSource m).measurableSet
    (fun x _ => ((markedRealStereoConeMap_contDiff m).differentiable
      (by simp) x).hasFDerivAt.hasFDerivWithinAt)
    (markedRealStereoConeMap_injOn m) g
  refine hh.trans ?_
  apply setLIntegral_congr_fun (isOpen_markedRealStereoConeSource m).measurableSet
  intro x hx
  dsimp only
  erw [markedRealStereoConeMap_fderiv_abs_det m x hx.1.le]

theorem markedRealStereoCone_gaussian_area (m : ℕ) :
    (∫⁻ y : ℝ × (Fin m → ℝ) in {y | 0 < y.1},
      ENNReal.ofReal (Real.exp (-markedRealProductEnergy m y))) =
      (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (r^m) *
        ENNReal.ofReal (Real.exp (-r^2))) *
      ∫⁻ u : Fin m → ℝ in {u | u ⬝ᵥ u < 1},
        ENNReal.ofReal ((2/markedRealStereoDenom m u)^m) := by
  rw [markedRealStereoCone_lintegral_image]
  simp_rw [markedRealStereoConeMap_energy]
  rw [markedRealStereoConeSource, Measure.volume_eq_prod, ← Measure.prod_restrict]
  have he (x : ℝ × (Fin m → ℝ)) :
      ENNReal.ofReal (x.1^m * (2/markedRealStereoDenom m x.2)^m) *
        ENNReal.ofReal (Real.exp (-x.1^2)) =
      (ENNReal.ofReal (x.1^m) * ENNReal.ofReal (Real.exp (-x.1^2))) *
        ENNReal.ofReal ((2/markedRealStereoDenom m x.2)^m) := by
    rw [ENNReal.ofReal_mul' (pow_nonneg (div_nonneg (by norm_num)
      (markedRealStereoDenom_pos m x.2).le) m)]
    ac_rfl
  simp_rw [he]
  exact lintegral_prod_mul
    (f := fun r : ℝ => ENNReal.ofReal (r^m) * ENNReal.ofReal (Real.exp (-r^2)))
    (g := fun u : Fin m → ℝ => ENNReal.ofReal ((2/markedRealStereoDenom m u)^m))
    (by fun_prop) (by
    have hd := (markedRealStereoDenom_contDiff m).continuous
    exact ((continuous_const.div hd (fun u => (markedRealStereoDenom_pos m u).ne')).pow m).measurable.ennreal_ofReal.aemeasurable)

#print axioms isOpen_markedRealStereoConeSource
#print axioms markedRealStereoCone_lintegral_image
#print axioms markedRealStereoCone_gaussian_area
end SpectralRadiusUpperTail
