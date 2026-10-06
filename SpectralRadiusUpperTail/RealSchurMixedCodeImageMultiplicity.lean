import SpectralRadiusUpperTail.RealSchurMixedCodeMultiplicity

namespace SpectralRadiusUpperTail
open scoped ENNReal Matrix Matrix.Norms.Operator

theorem realSchurMixedCodeClass_chart_image_eq
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (c : Fin m → ℝ) (hc : Function.Injective c)
    (R : ℕ → RealSchurMixedOrthogonalFrame s)
    (hcover : ∀ Q : RealSchurMixedOrthogonalFrame s, ∃ k,
      Q.val*realSchurMixedBlockScalar s c*Q.valᵀ ∈
        (realSchurMixedMarkerRotatedChart s hs c hc (R k).val (R k).property).target)
    (code : Fin m → Fin (Fintype.card (RealSchurMixedCoord s)) → Bool) :
    (⋃ k, realSchurMixedRotatedEntryCoordinates s 0 (R k).val (R k).property ''
      realSchurMixedFlagCodedSource s hs c hc R k code) =
      (realSchurMixedEntryEquiv s).symm ⁻¹' realSchurMixedCodeClass s code := by
  ext y
  have h := congrArg (fun V => (realSchurMixedEntryEquiv s).symm y ∈ V)
    (realSchurMixedCodeClass_eq_chart_preimage s hs c hc R hcover code)
  simpa only [Set.mem_preimage,LinearEquiv.apply_symm_apply] using iff_of_eq h.symm

theorem realSchurMixedCodeImageMultiplicity_eq
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (c : Fin m → ℝ) (hc : Function.Injective c)
    (R : ℕ → RealSchurMixedOrthogonalFrame s)
    (hcover : ∀ Q : RealSchurMixedOrthogonalFrame s, ∃ k,
      Q.val*realSchurMixedBlockScalar s c*Q.valᵀ ∈
        (realSchurMixedMarkerRotatedChart s hs c hc (R k).val (R k).property).target)
    (y : RealSchurMixedTangent s) :
    finiteCoverMultiplicity
      (fun code => ⋃ k, realSchurMixedRotatedEntryCoordinates s 0 (R k).val (R k).property ''
        realSchurMixedFlagCodedSource s hs c hc R k code) y =
      realSchurMixedCodeMultiplicity s ((realSchurMixedEntryEquiv s).symm y) := by
  classical
  apply Finset.sum_congr rfl
  intro code _
  dsimp only
  rw [realSchurMixedCodeClass_chart_image_eq s hs c hc R hcover code]
  rfl

/-- In any selected angle chart the intrinsic overlap count depends
only on its block-upper matrix, not on its orthogonal frame. -/
theorem realSchurMixedCodeMultiplicity_chart
    {m : ℕ} (s : Fin m → ℕ) (Q : RealSchurMixedOrthogonalFrame s)
    (x : RealSchurMixedTangent s) :
    realSchurMixedCodeMultiplicity s ((realSchurMixedEntryEquiv s).symm
      (realSchurMixedRotatedEntryCoordinates s 0 Q.val Q.property x)) =
      realSchurMixedCodeMultiplicity s x.2.val := by
  rw [realSchurMixedRotatedEntryCoordinates_eq,LinearEquiv.symm_apply_apply]
  let P : RealSchurMixedOrthogonalFrame s :=
    ⟨Q.val*realSchurMixedAngularFrame s x.1,realSchurMixed_rotatedFrame_orthogonal s Q x.1⟩
  have heq : Q.val*(realSchurMixedExpCoordinates s 0 x)*Q.valᵀ=P.val*x.2.val*P.valᵀ := by
    simp only [P,realSchurMixedExpCoordinates_eq_conjugation,zero_add,
      Matrix.transpose_mul,Matrix.mul_assoc]
  rw [heq,realSchurMixedCodeMultiplicity_orthogonal]

#print axioms realSchurMixedCodeClass_chart_image_eq
#print axioms realSchurMixedCodeImageMultiplicity_eq
#print axioms realSchurMixedCodeMultiplicity_chart
end SpectralRadiusUpperTail
