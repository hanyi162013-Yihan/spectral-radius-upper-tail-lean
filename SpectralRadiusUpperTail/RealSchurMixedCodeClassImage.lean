import SpectralRadiusUpperTail.RealSchurMixedCodeClassConnected
import SpectralRadiusUpperTail.RealSchurMixedFlagCodedCoverage
import SpectralRadiusUpperTail.RealSchurMixedFlagCodedIntegration

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Operator

/-- The intrinsic existence class agrees exactly with the union of the
selected injective angle-chart images. -/
theorem realSchurMixedCodeClass_eq_chart_preimage
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (c : Fin m → ℝ) (hc : Function.Injective c)
    (R : ℕ → RealSchurMixedOrthogonalFrame s)
    (hcover : ∀ Q : RealSchurMixedOrthogonalFrame s, ∃ k,
      Q.val*realSchurMixedBlockScalar s c*Q.valᵀ ∈
        (realSchurMixedMarkerRotatedChart s hs c hc (R k).val (R k).property).target)
    (code : Fin m → Fin (Fintype.card (RealSchurMixedCoord s)) → Bool) :
    realSchurMixedCodeClass s code = (realSchurMixedEntryEquiv s) ⁻¹'
      ⋃ k, realSchurMixedRotatedEntryCoordinates s 0 (R k).val (R k).property ''
        realSchurMixedFlagCodedSource s hs c hc R k code := by
  ext A
  constructor
  · rintro ⟨Q,T,hT,hsep,hcode,hrep⟩
    obtain ⟨k,x,hx,heq⟩ := realSchurMixedFlagCodedSource_coverage
      s hs c hc R hcover Q T hT hsep
    rw [hcode] at hx
    exact Set.mem_iUnion_of_mem k ⟨x,hx,by simpa only [← hrep] using heq⟩
  · intro hA
    obtain ⟨k,x,hx,heq⟩ := Set.mem_iUnion.mp hA
    let P : RealSchurMixedOrthogonalFrame s :=
      ⟨(R k).val*realSchurMixedAngularFrame s x.1,
        realSchurMixed_rotatedFrame_orthogonal s (R k) x.1⟩
    refine ⟨P,x.2.val,x.2.property,hx.2.1,hx.2.2,?_⟩
    rw [realSchurMixedRotatedEntryCoordinates_eq] at heq
    have h := (realSchurMixedEntryEquiv s).injective heq
    simpa only [P, realSchurMixedExpCoordinates_eq_conjugation, zero_add,
      Matrix.transpose_mul, Matrix.mul_assoc] using h.symm

theorem measurableSet_realSchurMixedCodeClass
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (code : Fin m → Fin (Fintype.card (RealSchurMixedCoord s)) → Bool) :
    MeasurableSet (realSchurMixedCodeClass s code) := by
  let c : Fin m → ℝ := fun i => i.val
  have hc : Function.Injective c := by
    intro i j h
    apply Fin.ext
    change (i.val : ℝ)=(j.val : ℝ) at h
    exact_mod_cast h
  obtain ⟨R,hR⟩ := exists_realSchurMixedFlagAtlasSequence s hs c hc
  rw [realSchurMixedCodeClass_eq_chart_preimage s hs c hc R hR code]
  apply MeasurableSet.preimage
    (MeasurableSet.iUnion (fun k => measurableSet_realSchurMixedFlagCodedImage s hs c hc R k code))
  exact (realSchurMixedEntryEquiv s).toContinuousLinearEquiv.continuous.measurable

#print axioms realSchurMixedCodeClass_eq_chart_preimage
#print axioms measurableSet_realSchurMixedCodeClass
end SpectralRadiusUpperTail
