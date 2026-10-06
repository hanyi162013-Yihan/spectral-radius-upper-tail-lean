import SpectralRadiusUpperTail.FiniteRightIsotropicProbability
import SpectralRadiusUpperTail.FiniteRightDeformationProbability
import SpectralRadiusUpperTail.ResolventQuantitative
import SpectralRadiusUpperTail.MatrixCoefficientDifference

namespace SpectralRadiusUpperTail
open scoped BigOperators Matrix Matrix.Norms.L2Operator
variable {n : ℕ}

lemma annulus_isotropic_add (A E : Matrix (Fin n) (Fin n) ℂ) (p q : Fin n → ℂ)
    (hp : (∑ i, ‖p i‖^2) ≤ 1) (hq : (∑ i, ‖q i‖^2) ≤ 1)
    (r L M ε : ℝ) (hM : 0 ≤ M) (hε : 0 < ε)
    (hb : matrixAnnulusControl A r L M)
    (hi : matrixAnnulusIsotropicControl A p q r L (ε/2))
    (hsmall : M*‖E‖ ≤ 1/2) (herr : 2*M^2*‖E‖ ≤ ε/4) :
    matrixAnnulusIsotropicControl (A+E) p q r L ε := by
  intro z hz hzL
  have hh := resolvent_add_quantitative A E z M hM (hb z hz hzL).1 (hb z hz hzL).2 hsmall
  refine ⟨hh.1,?_⟩
  have hc := (matrixCoefficient_difference_le p q hp hq
    (resolvent (A+E) z) (resolvent A z)).trans hh.2.2
  have hmain := (hi z hz hzL).2
  have htriangle := norm_add_le
    (matrixCoefficient p q (resolvent (A+E) z)-matrixCoefficient p q (resolvent A z))
    (matrixCoefficient p q (resolvent A z)-z⁻¹*matrixCoefficient p q 1)
  have he : matrixCoefficient p q (resolvent (A+E) z)-matrixCoefficient p q (resolvent A z)+
      (matrixCoefficient p q (resolvent A z)-z⁻¹*matrixCoefficient p q 1) =
      matrixCoefficient p q (resolvent (A+E) z)-z⁻¹*matrixCoefficient p q 1 := by ring
  rw [he] at htriangle
  linarith

#print axioms annulus_isotropic_add
end SpectralRadiusUpperTail
