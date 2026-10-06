import SpectralRadiusUpperTail.GramCanonicalSharpCode
import SpectralRadiusUpperTail.DefectCodePolynomialBound

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂] {m q : ℕ}

/-- A deliberately coarse absolute polynomial base suffices at logarithmic
trace order; the leading block factor remains sharp. -/
def gramDefectCountBase (m q : ℕ) := (64*(2*(q*m)+1))^72

lemma gram_nonzeroDefectPattern_count_le_polynomial (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hm : (∫ z : 𝕂, z ∂μ) = 0) (hq : 1 ≤ q) (g : ℕ)
    (hg : 1 ≤ g) (hgL : g ≤ 2*(q*m)) :
    Nat.card (NonzeroDefectPattern μ (gramTreeSign m q) g) ≤
      (m+1)^(2*q) * (gramDefectCountBase m q)^g := by
  let L := 2*(q*m)
  let B := 64*(L+1)
  have hB : L+1 ≤ B := by dsimp [B]; omega
  have hM : gramDefectMatchingCost m q g ≤ (m+1)^(2*q)*B^(8*g) :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hB _)
  have hcost : defectCodeCost L g ≤ B^(64*g) := defectCodeCost_power_le L g hg hgL
  calc
    Nat.card (NonzeroDefectPattern μ (gramTreeSign m q) g) ≤
        gramDefectMatchingCost m q g * defectCodeCost L g :=
      gram_nonzeroDefectPattern_count_le_explicit μ hm hq g
    _ ≤ ((m+1)^(2*q)*B^(8*g))*B^(64*g) := Nat.mul_le_mul hM hcost
    _ = (m+1)^(2*q)*(gramDefectCountBase m q)^g := by
      rw [Nat.mul_assoc,← pow_add]
      change (m+1)^(2*q)*B^(8*g+64*g) = (m+1)^(2*q)*(B^72)^g
      rw [← pow_mul]
      congr 2
      omega

#print axioms gramDefectCountBase
#print axioms gram_nonzeroDefectPattern_count_le_polynomial
end SpectralRadiusUpperTail
