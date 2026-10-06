import SpectralRadiusUpperTail.MatrixChainExpansion
import SpectralRadiusUpperTail.FiniteWordOrthogonality
import SpectralRadiusUpperTail.SchurBlockPathOrthogonality

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators

lemma matrixChain_pair_integrable {σ : Type*} [Fintype σ] [DecidableEq σ]
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hi : ∀ k : ℕ, Integrable (fun x : ℝ => x^k) μ)
    (d k l : ℕ) (D : Fin (k+1) → Matrix (Fin d) (Fin d) ℝ)
    (E : Fin (l+1) → Matrix (Fin d) (Fin d) ℝ)
    (e : Fin k → Fin d → Fin d → σ) (f : Fin l → Fin d → Fin d → σ)
    (a b c q : Fin d) :
    Integrable (fun x : σ → ℝ => gaussianMatrixChain d k D
      (fun j => Matrix.of (fun r s => x (e j r s))) a b *
      gaussianMatrixChain d l E (fun j => Matrix.of (fun r s => x (f j r s))) c q)
      (Measure.pi (fun _ => μ)) := by
  simp_rw [matrixChain_expansion]
  exact finite_word_pair_integrable μ hi (matrixChainCoefficient d k D a b)
    (matrixChainCoefficient d l E c q) (matrixChainWord d k e) (matrixChainWord d l f)

/-- Matrix-chain entries inherit orthogonality of the expanded scalar words. -/
theorem matrixChain_cross_zero {σ : Type*} [Fintype σ] [DecidableEq σ]
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hi : ∀ k : ℕ, Integrable (fun x : ℝ => x^k) μ)
    (d k l : ℕ) (D : Fin (k+1) → Matrix (Fin d) (Fin d) ℝ)
    (E : Fin (l+1) → Matrix (Fin d) (Fin d) ℝ)
    (e : Fin k → Fin d → Fin d → σ) (f : Fin l → Fin d → Fin d → σ)
    (hz : ∀ u : MatrixChainIndex d k, ∀ v : MatrixChainIndex d l,
      (∫ x : σ → ℝ, (∏ j, x (matrixChainWord d k e u j)) *
        (∏ j, x (matrixChainWord d l f v j)) ∂Measure.pi (fun _ => μ)) = 0)
    (a b c q : Fin d) :
    Integrable (fun x : σ → ℝ => gaussianMatrixChain d k D (fun j => Matrix.of (fun r s => x (e j r s))) a b *
      gaussianMatrixChain d l E (fun j => Matrix.of (fun r s => x (f j r s))) c q) (Measure.pi (fun _ => μ)) ∧
    (∫ x : σ → ℝ, gaussianMatrixChain d k D (fun j => Matrix.of (fun r s => x (e j r s))) a b *
      gaussianMatrixChain d l E (fun j => Matrix.of (fun r s => x (f j r s))) c q ∂Measure.pi (fun _ => μ)) = 0 := by
  simp_rw [matrixChain_expansion]
  exact finite_word_cross_zero μ hi (matrixChainCoefficient d k D a b)
    (matrixChainCoefficient d l E c q) (matrixChainWord d k e) (matrixChainWord d l f) hz

/-- Distinct increasing block paths ending at the same block have zero
entrywise cross moments, even when they share intermediate vertices or edges. -/
theorem schur_matrix_path_cross_zero {σ : Type*} [Fintype σ] [DecidableEq σ]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hm : (∫ x : ℝ, x ∂μ) = 0)
    (hi : ∀ k : ℕ, Integrable (fun x : ℝ => x^k) μ)
    {n d k : ℕ} (π : σ → Fin n × Fin n)
    (p q : Fin (k+1) → Fin n) (hp : StrictMono p) (hq : StrictMono q)
    (hlast : p (Fin.last k) = q (Fin.last k)) (hne : p ≠ q)
    (D E : Fin (k+1) → Matrix (Fin d) (Fin d) ℝ)
    (e f : Fin k → Fin d → Fin d → σ)
    (he : ∀ j r s, π (e j r s) = increasingPathEdge p j)
    (hf : ∀ j r s, π (f j r s) = increasingPathEdge q j)
    (a b c v : Fin d) :
    Integrable (fun x : σ → ℝ => gaussianMatrixChain d k D (fun j => Matrix.of (fun r s => x (e j r s))) a b *
      gaussianMatrixChain d k E (fun j => Matrix.of (fun r s => x (f j r s))) c v) (Measure.pi (fun _ => μ)) ∧
    (∫ x : σ → ℝ, gaussianMatrixChain d k D (fun j => Matrix.of (fun r s => x (e j r s))) a b *
      gaussianMatrixChain d k E (fun j => Matrix.of (fun r s => x (f j r s))) c v ∂Measure.pi (fun _ => μ)) = 0 := by
  apply matrixChain_cross_zero μ hi d k k D E e f _ a b c v
  intro u w
  simpa only [star_trivial] using schur_block_path_cross_zero μ hm π
    (matrixChainWord d k e u) (matrixChainWord d k f w) p q hp hq
    (matrixChainWord_project d k π e (increasingPathEdge p) he u)
    (matrixChainWord_project d k π f (increasingPathEdge q) hf w) hlast hne

theorem schur_matrix_path_different_length_cross_zero {σ : Type*}
    [Fintype σ] [DecidableEq σ] (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℝ, x ∂μ) = 0)
    (hi : ∀ k : ℕ, Integrable (fun x : ℝ => x^k) μ)
    {n d k l : ℕ} (π : σ → Fin n × Fin n)
    (p : Fin (k+1) → Fin n) (q : Fin (l+1) → Fin n)
    (hp : StrictMono p) (hq : StrictMono q) (hkl : k ≠ l)
    (D : Fin (k+1) → Matrix (Fin d) (Fin d) ℝ)
    (E : Fin (l+1) → Matrix (Fin d) (Fin d) ℝ)
    (e : Fin k → Fin d → Fin d → σ) (f : Fin l → Fin d → Fin d → σ)
    (he : ∀ j r s, π (e j r s) = increasingPathEdge p j)
    (hf : ∀ j r s, π (f j r s) = increasingPathEdge q j)
    (a b c v : Fin d) :
    Integrable (fun x : σ → ℝ => gaussianMatrixChain d k D (fun j => Matrix.of (fun r s => x (e j r s))) a b *
      gaussianMatrixChain d l E (fun j => Matrix.of (fun r s => x (f j r s))) c v) (Measure.pi (fun _ => μ)) ∧
    (∫ x : σ → ℝ, gaussianMatrixChain d k D (fun j => Matrix.of (fun r s => x (e j r s))) a b *
      gaussianMatrixChain d l E (fun j => Matrix.of (fun r s => x (f j r s))) c v ∂Measure.pi (fun _ => μ)) = 0 := by
  apply matrixChain_cross_zero μ hi d k l D E e f _ a b c v
  intro u w
  simpa only [star_trivial] using schur_block_path_different_length_cross_zero μ hm π
    (matrixChainWord d k e u) (matrixChainWord d l f w) p q hp hq
    (matrixChainWord_project d k π e (increasingPathEdge p) he u)
    (matrixChainWord_project d l π f (increasingPathEdge q) hf w) hkl

#print axioms schur_matrix_path_cross_zero
#print axioms schur_matrix_path_different_length_cross_zero
end SpectralRadiusUpperTail
