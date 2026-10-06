import SpectralRadiusUpperTail.MarkedRealStereoConeEnergy

namespace SpectralRadiusUpperTail
open scoped Matrix BigOperators

theorem markedRealStereoConeMap_surjOn (m : ℕ) :
    Set.SurjOn (markedRealStereoConeMap m) (markedRealStereoConeSource m)
      {y | 0 < y.1} := by
  intro y hy
  have hypos : 0 < y.1 := hy
  have hsum : 0 ≤ ∑ i : Fin m, (y.2 i)^2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hepos : 0 < markedRealProductEnergy m y := by
    unfold markedRealProductEnergy
    nlinarith [sq_pos_of_pos hypos]
  let r := Real.sqrt (markedRealProductEnergy m y)
  have hr : 0 < r := Real.sqrt_pos.mpr hepos
  have hrsq : r^2 = markedRealProductEnergy m y := Real.sq_sqrt hepos.le
  let v := markedRealVectorProductEquiv m y
  let q := fun i => v i / r
  have hunit : (∑ i, (q i)^2) = 1 := by
    simp only [q, div_pow, ← Finset.sum_div]
    rw [← markedRealProductEnergy_eq_column, ← hrsq]
    exact div_self (pow_ne_zero _ hr.ne')
  have hqpos : 0 < q (markedRealFirstCoordinate m) := by
    change 0 < y.1 / r
    exact div_pos hypos hr
  obtain ⟨u, hu, hcol⟩ :=
    markedRealStereoFrame_covers_positive_unit_column m q hunit hqpos
  refine ⟨(r,u), ⟨hr,hu⟩, ?_⟩
  apply (markedRealVectorProductEquiv m).injective
  change markedRealVectorProductEquiv m
    ((markedRealVectorProductEquiv m).symm (r • markedRealStereoColumn m u)) = v
  rw [LinearEquiv.apply_symm_apply]
  funext i
  change r * markedRealStereoFrame m u i (markedRealFirstCoordinate m) = v i
  rw [hcol]
  dsimp [q]
  field_simp

theorem markedRealStereoConeMap_image (m : ℕ) :
    markedRealStereoConeMap m '' markedRealStereoConeSource m = {y | 0 < y.1} :=
  Set.Subset.antisymm (markedRealStereoConeMap_mapsTo m).image_subset
    (markedRealStereoConeMap_surjOn m)

#print axioms markedRealStereoConeMap_surjOn
#print axioms markedRealStereoConeMap_image
end SpectralRadiusUpperTail
