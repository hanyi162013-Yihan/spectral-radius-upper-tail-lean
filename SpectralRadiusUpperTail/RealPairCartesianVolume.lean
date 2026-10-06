import SpectralRadiusUpperTail.RealPairEntryVolume
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.MeasureTheory.Group.Measure

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix

noncomputable def realPairSumDifference : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ).prod
    (ContinuousLinearMap.fst ℝ ℝ ℝ - ContinuousLinearMap.snd ℝ ℝ ℝ)

theorem realPairSumDifference_apply (z : ℝ × ℝ) :
    realPairSumDifference z=(z.1+z.2,z.1-z.2) := rfl

theorem realPairSumDifference_det : realPairSumDifference.det = -2 := by
  have hM : LinearMap.toMatrix (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ)
      realPairSumDifference.toLinearMap = !![1,1;1,-1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [LinearMap.toMatrix_apply,realPairSumDifference_apply,
        Module.Basis.finTwoProd_zero,Module.Basis.finTwoProd_one]
  rw [ContinuousLinearMap.det,← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ),hM]
  norm_num [Matrix.det_fin_two]

private theorem realPairSumDifference_surjective : Function.Surjective realPairSumDifference := by
  intro z
  refine ⟨((z.1+z.2)/2,(z.1-z.2)/2),?_⟩
  rw [realPairSumDifference_apply]
  apply Prod.ext <;> dsimp <;> ring

private theorem realPairSumDifference_injective : Function.Injective realPairSumDifference := by
  intro z w h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  change z.1+z.2=w.1+w.2 at h₁
  change z.1-z.2=w.1-w.2 at h₂
  apply Prod.ext <;> linarith

/-- The exact four-dimensional entry Jacobian is four. -/
theorem realPairCartesian_lintegral (g : ((Fin 2 × Fin 2) → ℝ) → ℝ≥0∞) :
    (∫⁻ A, g A) = 4 *
      ∫⁻ z : (ℝ × ℝ) × (ℝ × ℝ),
        g (fun ij => realPairCartesianMatrix z.1.1 z.1.2 z.2.1 z.2.2 ij.1 ij.2) := by
  letI : Measure.IsAddHaarMeasure (volume : Measure (ℝ × ℝ)) := by
    change Measure.IsAddHaarMeasure ((volume : Measure ℝ).prod volume)
    infer_instance
  letI : Measure.IsAddHaarMeasure (volume : Measure ((ℝ × ℝ) × (ℝ × ℝ))) := by
    change Measure.IsAddHaarMeasure ((volume : Measure (ℝ × ℝ)).prod volume)
    infer_instance
  let L := realPairSumDifference.prodMap realPairSumDifference
  have hdet : L.det=4 := by
    change (LinearMap.prodMap realPairSumDifference.toLinearMap
      realPairSumDifference.toLinearMap).det=4
    rw [LinearMap.det_prodMap]
    change realPairSumDifference.det * realPairSumDifference.det=4
    rw [realPairSumDifference_det]
    norm_num
  have hinj : Function.Injective L := by
    intro x y h
    exact Prod.ext (realPairSumDifference_injective (congrArg Prod.fst h))
      (realPairSumDifference_injective (congrArg Prod.snd h))
  have hsurj : Function.Surjective L := by
    intro z
    obtain ⟨x,hx⟩ := realPairSumDifference_surjective z.1
    obtain ⟨y,hy⟩ := realPairSumDifference_surjective z.2
    exact ⟨(x,y),Prod.ext hx hy⟩
  have harea := lintegral_image_eq_lintegral_abs_det_fderiv_mul
    (s := Set.univ) (f := L) (f' := fun _ => L) volume MeasurableSet.univ
    (fun _ _ => L.hasFDerivAt.hasFDerivWithinAt) hinj.injOn
    (fun z => g (realPairEntryProductEquiv z))
  rw [Set.image_univ,hsurj.range_eq,setLIntegral_univ,setLIntegral_univ,hdet] at harea
  have hpoint (z : (ℝ × ℝ) × (ℝ × ℝ)) :
      realPairEntryProductEquiv (L z) =
        fun ij => realPairCartesianMatrix z.1.1 z.1.2 z.2.1 z.2.2 ij.1 ij.2 := by
    funext ij
    rcases ij with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;>
      simp [L,realPairSumDifference_apply,realPairEntryProductEquiv,realPairCartesianMatrix]
  rw [realPairEntryProduct_lintegral,harea]
  simp_rw [hpoint]
  simp only [show |(4 : ℝ)|=4 by norm_num,ENNReal.ofReal_ofNat]
  exact lintegral_const_mul' 4 _ (by norm_num)

#print axioms realPairSumDifference_apply
#print axioms realPairSumDifference_det
#print axioms realPairCartesian_lintegral
end SpectralRadiusUpperTail
