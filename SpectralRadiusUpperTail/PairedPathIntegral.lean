import SpectralRadiusUpperTail.PairedAssignmentIntegrable
import SpectralRadiusUpperTail.MatrixBilinearPairExpansion
import Mathlib.Tactic.Ring

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
variable {k n : ℕ}

noncomputable def pairedPathCoefficient (p q : Fin n → 𝕂)
    (x : (Fin (k+1) ⊕ Fin (k+1)) → Fin n) : 𝕂 :=
  (star (p (x (Sum.inl 0))) * q (x (Sum.inl (Fin.last k)))) *
    star (star (p (x (Sum.inr 0))) * q (x (Sum.inr (Fin.last k))))

lemma pairedPathCoefficient_norm (p q : Fin n → 𝕂)
    (x : (Fin (k+1) ⊕ Fin (k+1)) → Fin n) :
    ‖pairedPathCoefficient p q x‖ = pairedAssignmentWeight p q x := by
  simp only [pairedPathCoefficient, pairedAssignmentWeight, norm_mul, norm_star]
  ring

lemma pairedPathTerm_factor (p q : Fin n → 𝕂)
    (x : (Fin (k+1) ⊕ Fin (k+1)) → Fin n) (y : Fin n × Fin n → 𝕂) :
    matrixBilinearPathTerm (Matrix.of (fun i j => y (i,j))) p q k (fun a => x (Sum.inl a)) *
      star (matrixBilinearPathTerm (Matrix.of (fun i j => y (i,j))) p q k
        (fun a => x (Sum.inr a))) =
    pairedPathCoefficient p q x *
      ((∏ a : Fin k, y (x (Sum.inl a.castSucc),x (Sum.inl a.succ))) *
       (∏ a : Fin k, star (y (x (Sum.inr a.castSucc),x (Sum.inr a.succ))))) := by
  simp only [matrixBilinearPathTerm, pairedPathCoefficient, star_mul, star_star,
    star_prod, Matrix.of_apply]
  ring

lemma pairedPathTerm_integrable (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c)
    (hexp : Integrable (fun z : 𝕂 => Real.exp (c*‖z‖^2)) μ)
    (p q : Fin n → 𝕂) (x : (Fin (k+1) ⊕ Fin (k+1)) → Fin n) :
    Integrable (fun y : Fin n × Fin n → 𝕂 =>
      matrixBilinearPathTerm (Matrix.of (fun i j => y (i,j))) p q k (fun a => x (Sum.inl a)) *
        star (matrixBilinearPathTerm (Matrix.of (fun i j => y (i,j))) p q k
          (fun a => x (Sum.inr a)))) (Measure.pi (fun _ : Fin n × Fin n => μ)) := by
  simp_rw [pairedPathTerm_factor]
  exact (pairedAssignment_integrable μ c hc hexp x).const_mul _

lemma pairedPathTerm_integral_norm (μ : Measure 𝕂) (p q : Fin n → 𝕂)
    (x : (Fin (k+1) ⊕ Fin (k+1)) → Fin n) :
    ‖∫ y : Fin n × Fin n → 𝕂,
      matrixBilinearPathTerm (Matrix.of (fun i j => y (i,j))) p q k (fun a => x (Sum.inl a)) *
        star (matrixBilinearPathTerm (Matrix.of (fun i j => y (i,j))) p q k
          (fun a => x (Sum.inr a))) ∂Measure.pi (fun _ : Fin n × Fin n => μ)‖ =
    pairedAssignmentWeight p q x * ‖pairedAssignmentMoment μ x‖ := by
  simp_rw [pairedPathTerm_factor]
  rw [integral_const_mul, norm_mul, pairedPathCoefficient_norm]
  rfl

#print axioms pairedPathCoefficient
#print axioms pairedPathCoefficient_norm
#print axioms pairedPathTerm_factor
#print axioms pairedPathTerm_integrable
#print axioms pairedPathTerm_integral_norm
end SpectralRadiusUpperTail
