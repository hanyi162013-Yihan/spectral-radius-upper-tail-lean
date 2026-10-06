import SpectralRadiusUpperTail.RealSchurAtomicFlagSource

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Operator

theorem realSchurAtomicCodeTest_chart_iff
    {m : ℕ} (s : Fin m → ℕ)
    (code : Fin m → Fin (Fintype.card (RealSchurMixedCoord s)) → Bool)
    (Q : RealSchurMixedOrthogonalFrame s) (x : RealSchurMixedTangent s)
    (hsep : x.2.val.charpoly.Separable) :
    realSchurAtomicCodeTest s code ((realSchurMixedEntryEquiv s).symm
      (realSchurMixedRotatedEntryCoordinates s 0 Q.val Q.property x)) ↔
        realSchurAtomicCodeTest s code x.2.val := by
  rw [realSchurMixedRotatedEntryCoordinates_eq,LinearEquiv.symm_apply_apply]
  have hpoly : (Q.val*(realSchurMixedExpCoordinates s 0 x)*Q.valᵀ).charpoly=x.2.val.charpoly := by
    rw [realMatrixOrthogonalConjugation_charpoly _ _ _ Q.property,
      realSchurMixedExpCoordinates_eq_conjugation,
      realMatrixOrthogonalConjugation_charpoly _ _ _ (realSchurMixedAngularFrame_orthogonal s x.1),
      zero_add]
  exact realSchurAtomicCodeTest_iff_of_charpoly s code _ _ (hpoly.symm ▸ hsep) hsep hpoly

/-- The atomic source covers exactly the corresponding intrinsic
scalar/nonreal-pair class, retaining the previously proved injectivity. -/
theorem realSchurAtomicCodeClass_eq_chart_preimage
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (c : Fin m → ℝ) (hc : Function.Injective c)
    (R : ℕ → RealSchurMixedOrthogonalFrame s)
    (hcover : ∀ Q : RealSchurMixedOrthogonalFrame s, ∃ k,
      Q.val*realSchurMixedBlockScalar s c*Q.valᵀ ∈
        (realSchurMixedMarkerRotatedChart s hs c hc (R k).val (R k).property).target)
    (code : Fin m → Fin (Fintype.card (RealSchurMixedCoord s)) → Bool) :
    realSchurAtomicCodeClass s code = (realSchurMixedEntryEquiv s) ⁻¹'
      ⋃ k, realSchurMixedRotatedEntryCoordinates s 0 (R k).val (R k).property ''
        realSchurAtomicFlagSource s hs c hc R k code := by
  ext A
  constructor
  · intro hA
    have hC := hA.1
    rw [realSchurMixedCodeClass_eq_chart_preimage s hs c hc R hcover code] at hC
    obtain ⟨k,x,hx,heq⟩ := Set.mem_iUnion.mp hC
    have htest : realSchurAtomicCodeTest s code ((realSchurMixedEntryEquiv s).symm
        (realSchurMixedRotatedEntryCoordinates s 0 (R k).val (R k).property x)) := by
      rw [heq,LinearEquiv.symm_apply_apply]
      exact hA.2
    exact Set.mem_iUnion_of_mem k ⟨x,⟨hx,
      (realSchurAtomicCodeTest_chart_iff s code (R k) x hx.2.1).mp htest⟩,heq⟩
  · intro hA
    obtain ⟨k,x,hx,heq⟩ := Set.mem_iUnion.mp hA
    refine ⟨?_,?_⟩
    · rw [realSchurMixedCodeClass_eq_chart_preimage s hs c hc R hcover code]
      exact Set.mem_iUnion_of_mem k ⟨x,hx.1,heq⟩
    · have htest := (realSchurAtomicCodeTest_chart_iff s code (R k) x hx.1.2.1).mpr hx.2
      rwa [heq,LinearEquiv.symm_apply_apply] at htest

#print axioms realSchurAtomicCodeTest_chart_iff
#print axioms realSchurAtomicCodeClass_eq_chart_preimage
end SpectralRadiusUpperTail
