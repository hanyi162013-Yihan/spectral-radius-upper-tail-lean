import SpectralRadiusUpperTail.RealSchurFiniteCodeClass
import SpectralRadiusUpperTail.RealSchurFixedVolumeEquiv

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix Matrix.Norms.Operator

/-- Global integration over one intrinsic finite class, starting with
the original entry-array volume. The coded sources have full upper fibers. -/
theorem realSchurFiniteCode_lintegral
    {n : ℕ} (I : RealSchurFiniteCode n)
    (c : Fin I.1.blockCount → ℝ) (hc : Function.Injective c)
    (R : ℕ → RealSchurMixedOrthogonalFrame I.1.sizes)
    (hcover : ∀ Q : RealSchurMixedOrthogonalFrame I.1.sizes, ∃ k,
      Q.val*realSchurMixedBlockScalar I.1.sizes c*Q.valᵀ ∈
        (realSchurMixedMarkerRotatedChart I.1.sizes I.1.sizes_pos c hc (R k).val (R k).property).target)
    (g : ((Fin n × Fin n) → ℝ) → ℝ≥0∞) :
    (∫⁻ x in {x | Matrix.of x.curry ∈ realSchurFiniteCodeClass I}, g x) =
      ∑' k, ∫⁻ t in realSchurMixedFlagCodedSource I.1.sizes I.1.sizes_pos c hc R k I.2.2,
        ENNReal.ofReal (realSchurMixedJacobianWeight I.1.sizes 0 t) *
          g ((realSchurFixedToMixedLinearEquiv I.2.1).symm
            (realSchurMixedRotatedEntryCoordinates I.1.sizes 0 (R k).val (R k).property t))
          ∂realSchurMixedCoordinateVolume I.1.sizes := by
  let s := I.1.sizes
  let E := realSchurFixedToMixedLinearEquiv I.2.1
  let S := ⋃ k, realSchurMixedRotatedEntryCoordinates s 0 (R k).val (R k).property ''
    realSchurMixedFlagCodedSource s I.1.sizes_pos c hc R k I.2.2
  have hS : MeasurableSet S := MeasurableSet.iUnion
    (fun k => measurableSet_realSchurMixedFlagCodedImage s I.1.sizes_pos c hc R k I.2.2)
  have hset : {x : (Fin n × Fin n) → ℝ | Matrix.of x.curry ∈ realSchurFiniteCodeClass I} =
      E ⁻¹' S := by
    ext x
    change Matrix.reindex I.2.1 I.2.1 (Matrix.of x.curry) ∈ realSchurMixedCodeClass s I.2.2 ↔ E x ∈ S
    rw [realSchurMixedCodeClass_eq_chart_preimage s I.1.sizes_pos c hc R hcover I.2.2]
    change _ ↔ realSchurFixedToMixedLinearEquiv I.2.1 x ∈ S
    rw [realSchurFixedToMixedLinearEquiv_apply,realSchurFixedToMixedTangent_eq_reindex]
    rfl
  rw [hset]
  have htransport := realSchurFixedToMixedLinearEquiv_setLIntegral I.2.1 S hS (fun y => g (E.symm y))
  have htransport' : (∫⁻ x in E ⁻¹' S, g x) =
      ∫⁻ y in S, g (E.symm y) ∂realSchurMixedCoordinateVolume s := by
    simpa only [E,LinearEquiv.symm_apply_apply] using htransport
  rw [htransport']
  change (∫⁻ y in ⋃ k, realSchurMixedRotatedEntryCoordinates s 0 (R k).val (R k).property ''
    realSchurMixedFlagCodedSource s I.1.sizes_pos c hc R k I.2.2,
      g (E.symm y) ∂realSchurMixedCoordinateVolume s)=_
  rw [lintegral_iUnion
    (fun k => measurableSet_realSchurMixedFlagCodedImage s I.1.sizes_pos c hc R k I.2.2)
    (pairwise_realSchurMixedFlagCodedImage s I.1.sizes_pos c hc R I.2.2)]
  apply tsum_congr
  intro k
  exact realSchurMixed_lintegral_injective_rotated s I.1.sizes_pos 0 (R k).val
    (map_zero _) (R k).property _
    (measurableSet_realSchurMixedFlagCodedSource s I.1.sizes_pos c hc R k I.2.2)
    (realSchurMixedFlagCodedSource_injOn s I.1.sizes_pos c hc R k I.2.2) (fun y => g (E.symm y))

#print axioms realSchurFiniteCode_lintegral
end SpectralRadiusUpperTail
