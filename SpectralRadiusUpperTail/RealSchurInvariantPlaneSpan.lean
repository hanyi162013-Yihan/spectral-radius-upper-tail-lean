import SpectralRadiusUpperTail.RealSchurComplexEigenplaneIndependent
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- A nonreal eigenpair produces a real invariant submodule of exact
dimension two. This is the basis-free version of the first 2×2 Schur
block; choosing an orthonormal basis and iterating remain separate. -/
theorem realMatrix_nonrealEigenpair_invariant_plane
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (z : Fin n → ℂ) (ζ : ℂ)
    (hz : (A.map Complex.ofRealHom).mulVec z = ζ • z)
    (hz0 : z ≠ 0) (hIm : ζ.im ≠ 0) :
    ∃ P : Submodule ℝ (Fin n → ℝ), Module.finrank ℝ P = 2 ∧
      ∀ w ∈ P, A.mulVec w ∈ P := by
  let u : Fin n → ℝ := fun i => (z i).re
  let v : Fin n → ℝ := fun i => (z i).im
  let e : Fin 2 → (Fin n → ℝ) := ![u,v]
  let P : Submodule ℝ (Fin n → ℝ) := Submodule.span ℝ (Set.range e)
  have hLI : LinearIndependent ℝ e :=
    realMatrix_nonrealEigenvector_re_im_independent A z ζ hz hz0 hIm
  have hdim : Module.finrank ℝ P = 2 := by
    simpa [P] using (finrank_span_eq_card hLI)
  have hu : u ∈ P := Submodule.subset_span ⟨0, by simp [e]⟩
  have hv : v ∈ P := Submodule.subset_span ⟨1, by simp [e]⟩
  have hpair := realMatrix_complexEigenvector_re_im A z ζ hz
  change A.mulVec u = ζ.re • u - ζ.im • v ∧
    A.mulVec v = ζ.im • u + ζ.re • v at hpair
  have hAu : A.mulVec u ∈ P := by
    rw [hpair.1]
    exact P.sub_mem (P.smul_mem _ hu) (P.smul_mem _ hv)
  have hAv : A.mulVec v ∈ P := by
    rw [hpair.2]
    exact P.add_mem (P.smul_mem _ hu) (P.smul_mem _ hv)
  refine ⟨P,hdim,?_⟩
  intro w hw
  refine Submodule.span_induction (fun x hx => ?_) ?_
    (fun x y _ _ hx hy => ?_) (fun a x _ hx => ?_) hw
  · obtain ⟨i,rfl⟩ := hx
    fin_cases i
    · simpa [e] using hAu
    · simpa [e] using hAv
  · simp
  · rw [Matrix.mulVec_add]
    exact P.add_mem hx hy
  · rw [Matrix.mulVec_smul]
    exact P.smul_mem a hx

#print axioms realMatrix_nonrealEigenpair_invariant_plane
end SpectralRadiusUpperTail
