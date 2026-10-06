import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Constructions
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open Polynomial

/-- A continuously evaluated polynomial cannot change among the finitely
many monic divisors of a fixed nonzero polynomial in a small neighborhood.
No topology on the polynomial type itself is required. -/
theorem realPolynomial_monicDivisor_locally_constant
    {X : Type*} [TopologicalSpace X] (f : X → ℝ[X])
    (hf : ∀ t : ℝ, Continuous (fun x => (f x).eval t))
    (p : ℝ[X]) (hp : p ≠ 0) (x₀ : X) :
    ∃ V : Set X, IsOpen V ∧ x₀ ∈ V ∧
      ∀ x ∈ V, (f x).Monic → f x ∣ p → f x = f x₀ := by
  classical
  let J := {q : ℝ[X] // q.Monic ∧ q ∣ p}
  let : Fintype J := Polynomial.fintypeSubtypeMonicDvd p hp
  let S : Set (ℝ → ℝ) := Set.range (fun q : J => q.val.eval)
  have hS : S.Finite := Set.finite_range _
  have hclosed : IsClosed (S \ {(f x₀).eval}) :=
    (hS.subset Set.sdiff_subset).isClosed
  let F : X → (ℝ → ℝ) := fun x => (f x).eval
  have hF : Continuous F := continuous_pi hf
  let V := F ⁻¹' (S \ {(f x₀).eval})ᶜ
  refine ⟨V,hclosed.isOpen_compl.preimage hF,?_,?_⟩
  · change (f x₀).eval ∉ S \ {(f x₀).eval}
    simp
  · intro x hx hmonic hdvd
    by_contra hne
    have hvalue : (f x).eval ≠ (f x₀).eval := by
      intro h
      exact hne (Polynomial.funext (fun t => congrFun h t))
    apply hx
    refine ⟨?_,hvalue⟩
    exact ⟨⟨f x,hmonic,hdvd⟩,rfl⟩

/-- Characteristic-polynomial evaluation is continuous in matrix entries. -/
theorem realMatrix_charpoly_eval_continuous
    {ι : Type*} [Fintype ι] [DecidableEq ι] (t : ℝ) :
    Continuous (fun A : Matrix ι ι ℝ => A.charpoly.eval t) := by
  have h : Continuous (fun A : Matrix ι ι ℝ => Matrix.scalar ι t - A) :=
    continuous_const.sub continuous_id
  simpa only [Matrix.eval_charpoly] using h.matrix_det

#print axioms realPolynomial_monicDivisor_locally_constant
#print axioms realMatrix_charpoly_eval_continuous
end SpectralRadiusUpperTail
