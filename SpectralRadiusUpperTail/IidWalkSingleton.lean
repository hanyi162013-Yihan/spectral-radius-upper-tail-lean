import SpectralRadiusUpperTail.MatrixWalkProduct
import SpectralRadiusUpperTail.IidWordMoments
import Mathlib.Tactic.Ring

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {ι 𝕂 : Type*} [Fintype ι] [DecidableEq ι]
  [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]

/-- The ordered directed edges of a walk, including its initial vertex. -/
def matrixWalkEdge {k : ℕ} (i : ι) (v : Fin k → ι) (j : Fin k) : ι × ι :=
  ((Fin.cons i v : Fin (k+1) → ι) j.castSucc,
    (Fin.cons i v : Fin (k+1) → ι) j.succ)

/-- Actual paired matrix-walk contributions vanish when a directed entry
occurs exactly once across the two walks. -/
lemma iidMatrixWalk_singleton_zero (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hm : (∫ x : 𝕂, x ∂μ) = 0) (q s : ι → 𝕂)
    (k l : ℕ) (i j : ι) (v : Fin k → ι) (w : Fin l → ι) (edge : ι × ι)
    (he : entryMultiplicity (matrixWalkEdge i v) edge+
      entryMultiplicity (matrixWalkEdge j w) edge = 1) :
    (∫ x : ι × ι → 𝕂,
      matrixWalkTerm (Matrix.of (fun a b => x (a,b))) q k i v *
        star (matrixWalkTerm (Matrix.of (fun a b => x (a,b))) s l j w)
      ∂Measure.pi (fun _ : ι × ι => μ)) = 0 := by
  have hzero := iidWordPair_singleton_zero μ hm (matrixWalkEdge i v) (matrixWalkEdge j w) edge he
  have hf : (fun x : ι × ι → 𝕂 =>
      matrixWalkTerm (Matrix.of (fun a b => x (a,b))) q k i v *
        star (matrixWalkTerm (Matrix.of (fun a b => x (a,b))) s l j w)) =
      (fun x => (q ((Fin.cons i v : Fin (k+1) → ι) (Fin.last k))*
        star (s ((Fin.cons j w : Fin (l+1) → ι) (Fin.last l)))) *
        ((∏ a, x (matrixWalkEdge i v a))*(∏ b, star (x (matrixWalkEdge j w b))))) := by
    funext x
    rw [matrixWalkTerm_product, matrixWalkTerm_product]
    simp only [star_mul, star_prod, matrixWalkEdge, Matrix.of_apply]
    ring
  rw [hf, integral_const_mul, hzero, mul_zero]

#print axioms iidMatrixWalk_singleton_zero
end SpectralRadiusUpperTail
