import SpectralRadiusUpperTail.TraceResolventExpansion
import SpectralRadiusUpperTail.MatrixExteriorPowerBound

namespace SpectralRadiusUpperTail
open scoped BigOperators

/-- Uniform convergence of the normalized trace on an entire exterior disk. -/
def matrixTraceControl {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (r ε : ℝ) : Prop :=
  ∀ z : ℂ, r ≤ ‖z‖ → z ∈ resolventSet ℂ A ∧
    ‖normalizedMatrixTrace (resolvent A z)-z⁻¹‖ < ε

lemma matrixTraceControl_of_finite {n : ℕ} (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℂ)
    (r C ε : ℝ) (hr : 1 ≤ r) (hε : 0 < ε) (k : ℕ)
    (htail : (k+3 : ℝ)*C/r^(k+1) ≤ ε/2)
    (hbase : matrixExteriorControl A r C)
    (hpower : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (A^(k+1))‖ ≤ k+3)
    (hcoeff : ∀ j ∈ Finset.range k,
      ‖normalizedMatrixTrace (A^(j+1))‖ ≤ ε/(4*(k+1))) :
    matrixTraceControl A r ε := by
  intro z hz
  refine ⟨(hbase z hz).1,?_⟩
  have hh := normalizedTrace_resolvent_error_le hn A z k r (k+3) C hr hz
    (hbase z hz).1 hpower (hbase z hz).2
  have hs : (∑ j ∈ Finset.range k, ‖normalizedMatrixTrace (A^(j+1))‖) ≤
      (k : ℝ)*(ε/(4*(k+1))) := by
    simpa only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] using
      Finset.sum_le_sum hcoeff
  have hd : 0 < (4*(k+1 : ℝ)) := by positivity
  have he : (k+1 : ℝ)*(ε/(4*(k+1))) = ε/4 := by field_simp
  have hδ : 0 ≤ ε/(4*(k+1 : ℝ)) := by positivity
  have hsmall : (k : ℝ)*(ε/(4*(k+1))) ≤ ε/4 := by nlinarith
  linarith

#print axioms matrixTraceControl
#print axioms matrixTraceControl_of_finite
end SpectralRadiusUpperTail
