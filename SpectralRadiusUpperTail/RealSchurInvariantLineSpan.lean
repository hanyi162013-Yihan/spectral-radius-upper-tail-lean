import SpectralRadiusUpperTail.RealSchurComplexEigenline
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- A nonzero real eigenvector spans an invariant real line. -/
theorem realMatrix_realEigenvector_invariant_line
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (a : ℝ) (u : Fin n → ℝ)
    (hu : u ≠ 0) (hAu : A.mulVec u = a • u) :
    ∃ P : Submodule ℝ (Fin n → ℝ), Module.finrank ℝ P = 1 ∧
      ∀ w ∈ P, A.mulVec w ∈ P := by
  let P : Submodule ℝ (Fin n → ℝ) := Submodule.span ℝ {u}
  have hdim : Module.finrank ℝ P = 1 := by
    simpa [P] using (finrank_span_singleton hu)
  have hAuP : A.mulVec u ∈ P := by
    rw [hAu]
    exact P.smul_mem a (Submodule.subset_span (by simp))
  refine ⟨P,hdim,?_⟩
  intro w hw
  refine Submodule.span_induction (fun x hx => ?_) ?_
    (fun x y _ _ hx hy => ?_) (fun b x _ hx => ?_) hw
  · have : x = u := by simpa using hx
    subst x
    exact hAuP
  · simp
  · rw [Matrix.mulVec_add]
    exact P.add_mem hx hy
  · rw [Matrix.mulVec_smul]
    exact P.smul_mem b hx

#print axioms realMatrix_realEigenvector_invariant_line
end SpectralRadiusUpperTail
