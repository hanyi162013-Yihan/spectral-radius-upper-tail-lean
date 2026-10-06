import SpectralRadiusUpperTail.MatrixCoefficientCLM
import Mathlib.Analysis.Normed.Algebra.GelfandFormula

namespace SpectralRadiusUpperTail
open scoped BigOperators Matrix Matrix.Norms.L2Operator
variable {n : ℕ}

lemma hasDerivAt_resolvent_coefficient (A : Matrix (Fin n) (Fin n) ℂ) (p q : Fin n → ℂ)
    (hp : (∑ i, ‖p i‖^2) ≤ 1) (hq : (∑ i, ‖q i‖^2) ≤ 1)
    (z : ℂ) (hz : z ∈ resolventSet ℂ A) :
    HasDerivAt (fun w : ℂ => matrixCoefficient p q (resolvent A w))
      (matrixCoefficient p q (-(resolvent A z)^2)) z := by
  have hh := (matrixCoefficientCLM p q hp hq).hasFDerivAt.comp_hasDerivAt z
    (spectrum.hasDerivAt_resolvent_const_left hz)
  have he : (matrixCoefficientCLM p q hp hq) ∘ (resolvent A : ℂ → Matrix (Fin n) (Fin n) ℂ) =
      (fun w => matrixCoefficient p q (resolvent A w)) := by funext w; rfl
  rw [he] at hh
  exact hh

lemma differentiableOn_resolvent_coefficient (A : Matrix (Fin n) (Fin n) ℂ) (p q : Fin n → ℂ)
    (hp : (∑ i, ‖p i‖^2) ≤ 1) (hq : (∑ i, ‖q i‖^2) ≤ 1)
    (S : Set ℂ) (hS : ∀ z ∈ S, z ∈ resolventSet ℂ A) :
    DifferentiableOn ℂ (fun z => matrixCoefficient p q (resolvent A z)) S := by
  intro z hz
  exact (hasDerivAt_resolvent_coefficient A p q hp hq z (hS z hz)).differentiableAt.differentiableWithinAt

#print axioms hasDerivAt_resolvent_coefficient
#print axioms differentiableOn_resolvent_coefficient
end SpectralRadiusUpperTail
