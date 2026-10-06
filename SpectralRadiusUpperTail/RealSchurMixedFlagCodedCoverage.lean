import SpectralRadiusUpperTail.RealSchurMixedFlagRepresentation
import SpectralRadiusUpperTail.RealSchurMixedFlagCodedSource
import SpectralRadiusUpperTail.RealSchurMixedSpectralFiber

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Operator

/-- A simple block-upper representation is covered in its own finite
spectral class. Moving into the selected angle patch preserves that
class, every ordered block spectrum, and the represented matrix. -/
theorem realSchurMixedFlagCodedSource_coverage
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (c : Fin m → ℝ) (hc : Function.Injective c)
    (R : ℕ → RealSchurMixedOrthogonalFrame s)
    (hcover : ∀ Q : RealSchurMixedOrthogonalFrame s, ∃ k,
      Q.val*realSchurMixedBlockScalar s c*Q.valᵀ ∈
        (realSchurMixedMarkerRotatedChart s hs c hc (R k).val (R k).property).target)
    (Q : RealSchurMixedOrthogonalFrame s)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hT : realSchurMixedLowerProjection s T=0) (hsep : T.charpoly.Separable) :
    ∃ k, ∃ x ∈ realSchurMixedFlagCodedSource s hs c hc R k (realSchurMixedSpectralCode s T),
      realSchurMixedRotatedEntryCoordinates s 0 (R k).val (R k).property x =
        realSchurMixedEntryEquiv s (Q.val*T*Q.valᵀ) := by
  obtain ⟨k,w,hw,U,hU,hdiag,heq⟩ := realSchurMixedFlag_representation_coverage
    s hs c hc R hcover Q T ((realSchurMixed_blockTriangular_iff_lower_zero s T).mpr hT)
  have hU_lower : realSchurMixedLowerProjection s U=0 :=
    (realSchurMixed_blockTriangular_iff_lower_zero s U).mp hU
  have hd (a : Fin m) : (realSchurMixedDiagonalMatrix s U a).charpoly =
      (realSchurMixedDiagonalMatrix s T a).charpoly := by
    simpa only [realSchurMixedDiagonalMatrix_charpoly] using hdiag a
  have hpoly := realSchurMixed_charpoly_eq_of_diagonal_polynomials s hs U T hU_lower hT hd
  have hU_sep : U.charpoly.Separable := hpoly.symm ▸ hsep
  have hcode := realSchurMixedSpectralCode_eq_of_diagonal_polynomials s hs U T
    hU_lower hT hU_sep hd
  let x : RealSchurMixedTangent s := (w,⟨U,hU_lower⟩)
  refine ⟨k,x,⟨hw,hU_sep,hcode⟩,?_⟩
  rw [realSchurMixedRotatedEntryCoordinates_eq]
  apply congrArg (realSchurMixedEntryEquiv s)
  rw [realSchurMixedExpCoordinates_eq_conjugation, zero_add]
  simpa only [x, Matrix.transpose_mul, Matrix.mul_assoc] using heq.symm

#print axioms realSchurMixedFlagCodedSource_coverage
end SpectralRadiusUpperTail
