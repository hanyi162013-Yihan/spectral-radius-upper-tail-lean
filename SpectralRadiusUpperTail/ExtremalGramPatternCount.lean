import SpectralRadiusUpperTail.ExtremalPatternCount
import SpectralRadiusUpperTail.GramTreeSignCast

namespace SpectralRadiusUpperTail
open MeasureTheory
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]

/-- The number of actual nonzero closed maximal-vertex patterns for the Gram
word is bounded uniformly in q by (m+1)^(2q). Defective patterns are excluded
from this leading-tree count and still require a separate estimate. -/
lemma extremalGramPattern_count_le (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hm : (∫ z : 𝕂, z ∂μ) = 0) (m q : ℕ) :
    Nat.card (ExtremalClosedPattern μ (gramTreeSign m q)) ≤ (m+1)^(2*q) :=
  (extremalPattern_count_le_matching μ hm (gramTreeSign m q)).trans
    (gramTreeSign_matching_count_le m q)

#print axioms extremalGramPattern_count_le
end SpectralRadiusUpperTail
