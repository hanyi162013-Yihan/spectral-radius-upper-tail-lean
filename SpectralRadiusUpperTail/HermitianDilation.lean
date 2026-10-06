import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Analysis.RCLike.Basic

namespace SpectralRadiusUpperTail
open Matrix
variable {𝕂 : Type*} [RCLike 𝕂] {ι : Type*} [Fintype ι]

/-- The actual self-adjoint block dilation of a square matrix. -/
def hermitianDilation (A : Matrix ι ι 𝕂) : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝕂 :=
  Matrix.fromBlocks 0 A A.conjTranspose 0

lemma hermitianDilation_isHermitian (A : Matrix ι ι 𝕂) :
    (hermitianDilation A).IsHermitian := by
  exact Matrix.IsHermitian.fromBlocks (by simp) rfl (by simp)

lemma hermitianDilation_square (A : Matrix ι ι 𝕂) :
    hermitianDilation A * hermitianDilation A =
      Matrix.fromBlocks (A*A.conjTranspose) 0 0 (A.conjTranspose*A) := by
  simp [hermitianDilation, Matrix.fromBlocks_multiply]

/-- Real linearity is essential in the complex case: the lower block is
conjugate transpose. The normed codomain is the finite function space. -/
noncomputable def hermitianDilationL : (ι → ι → 𝕂) →L[ℝ] ((ι ⊕ ι) → (ι ⊕ ι) → 𝕂) :=
  let ev (i j : ι) : (ι → ι → 𝕂) →L[ℝ] 𝕂 :=
    (ContinuousLinearMap.proj j : (ι → 𝕂) →L[ℝ] 𝕂).comp
      (ContinuousLinearMap.proj i : (ι → ι → 𝕂) →L[ℝ] (ι → 𝕂))
  ContinuousLinearMap.pi fun p => ContinuousLinearMap.pi fun q =>
    match p, q with
    | Sum.inl i, Sum.inr j => ev i j
    | Sum.inr j, Sum.inl i => RCLike.conjCLE.toContinuousLinearMap.comp (ev i j)
    | _, _ => 0

lemma hermitianDilationL_apply (A : ι → ι → 𝕂) :
    hermitianDilationL A = hermitianDilation A := by
  ext p q
  cases p <;> cases q <;> rfl

#print axioms hermitianDilation_square
#print axioms hermitianDilationL
end SpectralRadiusUpperTail
