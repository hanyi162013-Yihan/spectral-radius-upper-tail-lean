import SpectralRadiusUpperTail.MarkedRealStereoConeMap

namespace SpectralRadiusUpperTail
open scoped Matrix BigOperators

def markedRealProductEnergy (m : ℕ) (x : ℝ × (Fin m → ℝ)) : ℝ :=
  x.1^2 + ∑ i, (x.2 i)^2

theorem markedRealProductEnergy_eq_column (m : ℕ) (x : ℝ × (Fin m → ℝ)) :
    markedRealProductEnergy m x = ∑ i, (markedRealVectorProductEquiv m x i)^2 :=
  (markedRealVectorCons_sum m x.1 x.2 (fun t => t^2)).symm

theorem markedRealStereoConeMap_energy (m : ℕ) (x : ℝ × (Fin m → ℝ)) :
    markedRealProductEnergy m (markedRealStereoConeMap m x) = x.1^2 := by
  rw [markedRealProductEnergy_eq_column]
  have he : markedRealVectorProductEquiv m (markedRealStereoConeMap m x) =
      x.1 • markedRealStereoColumn m x.2 := LinearEquiv.apply_symm_apply _ _
  rw [he]
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum,
    markedRealStereoColumn_unit, mul_one]

theorem markedRealStereoConeMap_injOn (m : ℕ) :
    Set.InjOn (markedRealStereoConeMap m) (markedRealStereoConeSource m) := by
  intro x hx y hy heq
  have he := congrArg (markedRealProductEnergy m) heq
  rw [markedRealStereoConeMap_energy, markedRealStereoConeMap_energy] at he
  have hxpos : 0 < x.1 := hx.1
  have hypos : 0 < y.1 := hy.1
  have hxy : x.1 = y.1 := by nlinarith
  have hv := congrArg (markedRealVectorProductEquiv m) heq
  simp only [markedRealStereoConeMap, LinearEquiv.apply_symm_apply] at hv
  have hcol : markedRealStereoColumn m x.2 = markedRealStereoColumn m y.2 := by
    funext i
    have hi := congrFun hv i
    change x.1*markedRealStereoColumn m x.2 i = y.1*markedRealStereoColumn m y.2 i at hi
    rw [hxy] at hi
    exact (mul_left_cancel₀ hypos.ne') hi
  have hu : x.2 = y.2 := markedRealStereoFrame_firstColumn_injective m hcol
  exact Prod.ext hxy hu

theorem markedRealStereoConeMap_mapsTo (m : ℕ) :
    Set.MapsTo (markedRealStereoConeMap m) (markedRealStereoConeSource m)
      {y | 0 < y.1} := by
  intro x hx
  change 0 < x.1 * markedRealStereoFrame m x.2
    (markedRealFirstCoordinate m) (markedRealFirstCoordinate m)
  exact mul_pos hx.1 (markedRealStereoFrame_first_positive m x.2 hx.2)

#print axioms markedRealProductEnergy_eq_column
#print axioms markedRealStereoConeMap_energy
#print axioms markedRealStereoConeMap_injOn
#print axioms markedRealStereoConeMap_mapsTo
end SpectralRadiusUpperTail
