import SpectralRadiusUpperTail.RealSchurPrefixFrame
import SpectralRadiusUpperTail.RealSchurCoprimeInvariantFlags
import SpectralRadiusUpperTail.RealSchurOrthogonalFlagTransition
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- Two orthogonal block-upper representations of the same matrix have
the same ordered block flag when each prefix spectrum is disjoint from
the other representation's trailing quotient spectrum. Their relative
frame can therefore rotate only inside diagonal blocks. -/
theorem realSchurOrderedOverlap_offBlock
    {ι β : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder β]
    (b : ι → β) (A Q R T U : Matrix ι ι ℝ)
    (hQ : Qᵀ*Q=1) (hR : Rᵀ*R=1)
    (hT : T.BlockTriangular b) (hU : U.BlockTriangular b)
    (hAQ : A=Q*T*Qᵀ) (hAR : A=R*U*Rᵀ)
    (hQR : ∀ k : β,
      IsCoprime
        ((A.mulVecLin).restrict
          (realSchurPrefixSpan_invariant b A Q T hQ hT hAQ k)).charpoly
        (realLinearMapInvariantQuotient A.mulVecLin
          (realSchurPrefixSpan b R k)
          (realSchurPrefixSpan_invariant b A R U hR hU hAR k)).charpoly)
    (hRQ : ∀ k : β,
      IsCoprime
        ((A.mulVecLin).restrict
          (realSchurPrefixSpan_invariant b A R U hR hU hAR k)).charpoly
        (realLinearMapInvariantQuotient A.mulVecLin
          (realSchurPrefixSpan b Q k)
          (realSchurPrefixSpan_invariant b A Q T hQ hT hAQ k)).charpoly)
    (i j : ι) (hij : b i ≠ b j) :
    (Qᵀ*R) i j = 0 := by
  have hflags : ∀ k : β,
      realSchurPrefixSpan b Q k = realSchurPrefixSpan b R k := by
    intro k
    exact invariantSubmodules_eq_of_cross_coprime_charpoly
      A.mulVecLin (realSchurPrefixSpan b Q k)
      (realSchurPrefixSpan b R k)
      (realSchurPrefixSpan_invariant b A Q T hQ hT hAQ k)
      (realSchurPrefixSpan_invariant b A R U hR hU hAR k)
      (hQR k) (hRQ k)
  exact orthogonal_equalBlockFlags_transition_offBlock b Q R hQ hR
    hflags i j hij

#print axioms realSchurOrderedOverlap_offBlock
end SpectralRadiusUpperTail
