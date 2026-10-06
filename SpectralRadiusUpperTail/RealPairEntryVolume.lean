import SpectralRadiusUpperTail.RealPairNonrealCoordinates
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix

/-- The two diagonal entries and the two off-diagonal entries, grouped
as two independent pairs, are just a permutation of the original entries. -/
def realPairEntryProductEquiv : ((ℝ × ℝ) × (ℝ × ℝ)) ≃ᵐ ((Fin 2 × Fin 2) → ℝ) where
  toFun z := fun ij => if ij.1=0 then (if ij.2=0 then z.1.1 else z.2.1)
    else (if ij.2=0 then z.2.2 else z.1.2)
  invFun f := ((f (0,0),f (1,1)),(f (0,1),f (1,0)))
  left_inv z := by simp
  right_inv f := by
    funext ij
    rcases ij with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;> simp
  measurable_toFun := by
    change Measurable (fun z : (ℝ × ℝ) × (ℝ × ℝ) => fun ij : Fin 2 × Fin 2 =>
      if ij.1=0 then (if ij.2=0 then z.1.1 else z.2.1)
      else (if ij.2=0 then z.2.2 else z.1.2))
    apply measurable_pi_lambda
    intro ij
    split_ifs <;> fun_prop
  measurable_invFun := by
    change Measurable (fun f : (Fin 2 × Fin 2) → ℝ =>
      ((f (0,0),f (1,1)),(f (0,1),f (1,0))))
    fun_prop

theorem realPairEntryProductEquiv_measurePreserving :
    MeasurePreserving realPairEntryProductEquiv := by
  refine ⟨realPairEntryProductEquiv.measurable,?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply realPairEntryProductEquiv.measurable (MeasurableSet.univ_pi hs)]
  have he : realPairEntryProductEquiv ⁻¹' Set.pi Set.univ s =
      (s (0,0) ×ˢ s (1,1)) ×ˢ (s (0,1) ×ˢ s (1,0)) := by
    ext z
    simp only [Set.mem_preimage,Set.mem_pi,Set.mem_univ,forall_const,Prod.forall,
      Fin.forall_fin_two,realPairEntryProductEquiv,MeasurableEquiv.coe_mk,
      Equiv.coe_fn_mk,Set.mem_prod]
    simp only [ite_true,ite_false,show (1 : Fin 2) ≠ 0 by decide]
    tauto
  rw [he]
  symm
  change (∏ i : Fin 2 × Fin 2, (volume : Measure ℝ) (s i)) =
    ((volume : Measure (ℝ × ℝ)).prod volume)
      ((s (0,0) ×ˢ s (1,1)) ×ˢ (s (0,1) ×ˢ s (1,0)))
  rw [Measure.prod_prod]
  change _ = ((volume : Measure ℝ).prod volume) (s (0,0) ×ˢ s (1,1)) *
    ((volume : Measure ℝ).prod volume) (s (0,1) ×ˢ s (1,0))
  rw [Measure.prod_prod,Measure.prod_prod]
  simp only [Fintype.prod_prod_type,Fin.prod_univ_two]
  ac_rfl

theorem realPairEntryProduct_lintegral (g : ((Fin 2 × Fin 2) → ℝ) → ℝ≥0∞) :
    (∫⁻ A, g A) = ∫⁻ z : (ℝ × ℝ) × (ℝ × ℝ), g (realPairEntryProductEquiv z) :=
  realPairEntryProductEquiv_measurePreserving.lintegral_map_equiv g realPairEntryProductEquiv

#print axioms realPairEntryProductEquiv_measurePreserving
#print axioms realPairEntryProduct_lintegral
end SpectralRadiusUpperTail
