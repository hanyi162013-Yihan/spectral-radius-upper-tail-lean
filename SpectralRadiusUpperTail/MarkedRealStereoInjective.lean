import SpectralRadiusUpperTail.MarkedRealStereoMatrixMap
import SpectralRadiusUpperTail.MarkedRealAngularRankSource

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Operator

theorem markedRealStereo_injective_at_root (m : ℕ)
    (w v : RealSchurMixedOrbitIndex (markedRealTwoBlockSizes m) → ℝ)
    (S T : realSchurMixedUpperSubmodule (markedRealTwoBlockSizes m))
    (hw : w ∈ markedRealStereoSource m) (hv : v ∈ markedRealStereoSource m)
    (hscalar : markedRealScalar m S.val = markedRealScalar m T.val)
    (heq : markedRealStereoMatrixMap m (w,S) = markedRealStereoMatrixMap m (v,T))
    (hsep : (markedRealStereoMatrixMap m (w,S)).charpoly.Separable) :
    w = v ∧ S = T := by
  let Q := markedRealStereoNativeFrame m w
  let R := markedRealStereoNativeFrame m v
  have hQ : Qᵀ*Q=1 := markedRealStereoNativeFrame_orthogonal m w
  have hR : Rᵀ*R=1 := markedRealStereoNativeFrame_orthogonal m v
  have hcol := markedRealUpper_rotatedColumns_eq_of_sameRoot m
    (Q*S.val*Qᵀ) Q R S.val T.val hsep S.property T.property hQ hR rfl heq
      hscalar (markedRealStereoNativeFrame_first_positive m w hw)
        (markedRealStereoNativeFrame_first_positive m v hv)
  have hwv : w = v := markedRealStereoNativeFrame_firstColumn_injective m (funext hcol)
  refine ⟨hwv, ?_⟩
  subst v
  apply Subtype.ext
  have hQT := congrArg (fun X => Qᵀ*X*Q) heq
  change Qᵀ*(Q*S.val*Qᵀ)*Q = Qᵀ*(Q*T.val*Qᵀ)*Q at hQT
  simpa only [Matrix.mul_assoc,
    ← Matrix.mul_assoc Qᵀ Q, hQ, Matrix.one_mul, Matrix.mul_one] using hQT

/-- Root rank removes the ambiguity between distinct real eigenvalues,
while the hemisphere coordinates remove the eigenvector sign ambiguity. -/
theorem markedRealStereoMatrixMap_injOn_rank (m k : ℕ) (hm : 0 < m) (b : ℝ) :
    Set.InjOn (markedRealStereoMatrixMap m)
      (markedRealStereoSource m ×ˢ markedRealUpperRankSource m k b) := by
  rintro ⟨w,S⟩ hp ⟨v,T⟩ hq heq
  have hpoly : S.val.charpoly = T.val.charpoly := by
    have h := congrArg Matrix.charpoly heq
    simpa only [markedRealStereoMatrixMap,
      realMatrixOrthogonalConjugation_charpoly _ _ _
        (markedRealStereoNativeFrame_orthogonal _ _)] using h
  have hscalar : markedRealScalar m S.val = markedRealScalar m T.val := by
    apply realPolynomialRootRank_injective_on_roots S.val.charpoly
      S.val.charpoly_monic.ne_zero
      (markedRealScalar m S.val) (markedRealScalar m T.val)
      (markedRealUpper_scalar_isRoot m hm S)
      (hpoly ▸ markedRealUpper_scalar_isRoot m hm T)
    rw [hp.2.2.2, hpoly, hq.2.2.2]
  have hsep : (markedRealStereoMatrixMap m (w,S)).charpoly.Separable := by
    rw [markedRealStereoMatrixMap, realMatrixOrthogonalConjugation_charpoly _ _ _
      (markedRealStereoNativeFrame_orthogonal m w)]
    exact hp.2.1
  obtain ⟨hwv,hST⟩ := markedRealStereo_injective_at_root m w v S T
    hp.1 hq.1 hscalar heq hsep
  exact Prod.ext hwv hST

theorem markedRealStereoEntryMap_injOn_rank (m k : ℕ) (hm : 0 < m) (b : ℝ) :
    Set.InjOn (markedRealStereoEntryMap m)
      (markedRealStereoSource m ×ˢ markedRealUpperRankSource m k b) := by
  intro x hx y hy heq
  exact markedRealStereoMatrixMap_injOn_rank m k hm b hx hy
    ((realSchurMixedEntryEquiv (markedRealTwoBlockSizes m)).injective heq)

#print axioms markedRealStereo_injective_at_root
#print axioms markedRealStereoMatrixMap_injOn_rank
#print axioms markedRealStereoEntryMap_injOn_rank
end SpectralRadiusUpperTail
