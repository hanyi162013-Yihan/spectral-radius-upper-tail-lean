import SpectralRadiusUpperTail.GaussianHermitianIncrement

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped MeasureTheory
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂] {N : ℕ}

/-- An explicitly matrix-typed product, used even when the surrounding
Bochner space is represented as a finite function space. -/
def matrixSelfProduct {ι : Type*} [Fintype ι] (A : Matrix ι ι 𝕂) : Matrix ι ι 𝕂 := A*A

/-- Actual matrix multiplication of the actual Hermitian increment by itself. -/
noncomputable def gaussianHermitianCoordinateSquare (μ : Measure 𝕂) [SFinite μ]
    (v : ℕ → 𝕂) (a : ℝ) (t : Fin N → 𝕂) (K R : ℝ) (i n : Fin N)
    (x : Fin N → Fin N → 𝕂 × 𝕂) : (Fin N ⊕ Fin N) → (Fin N ⊕ Fin N) → 𝕂 :=
  matrixSelfProduct (gaussianHermitianCoordinateIncrement μ v a t K R i n x)

lemma gaussianHermitianCoordinateSquare_eq (μ : Measure 𝕂) [SFinite μ]
    (v : ℕ → 𝕂) (a : ℝ) (t : Fin N → 𝕂) (K R : ℝ) (i n : Fin N) :
    gaussianHermitianCoordinateSquare μ v a t K R i n =
      (((N : ℝ)⁻¹ • dilationVarianceCoordinateL (𝕂 := 𝕂) i n.rev) ∘
        (fun x => ‖gaussianMatrixTruncatedEntry μ v a t K R i n.val x‖^2)) := by
  funext x
  change matrixSelfProduct (hermitianDilationL _) = _
  rw [hermitianDilationL_apply]
  unfold matrixSelfProduct
  change hermitianDilation ((Real.sqrt (N : ℝ))⁻¹ • matrixCoordinateL i n.rev
      (gaussianMatrixTruncatedEntry μ v a t K R i n.val x)) *
    hermitianDilation ((Real.sqrt (N : ℝ))⁻¹ • matrixCoordinateL i n.rev
      (gaussianMatrixTruncatedEntry μ v a t K R i n.val x)) = _
  rw [scaled_matrixCoordinate_dilation_square]
  rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
  rfl

/-- The actual conditional squared matrix increment is the continuous
linear image of its scalar conditional second moment, under the full past. -/
theorem gaussianHermitianCoordinateSquare_condExp
    (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (v : ℕ → 𝕂) (a : ℝ) (ha : 0 < a)
    (t : Fin N → 𝕂) (K R : ℝ) (hR : 0 ≤ R) (i n : Fin N) :
    Integrable (gaussianHermitianCoordinateSquare μ v a t K R i n)
      (gaussianSequentialMatrixLaw μ v a t) ∧
      (gaussianSequentialMatrixLaw μ v a t)[gaussianHermitianCoordinateSquare μ v a t K R i n |
        rowMajorFiltration N N (i.val*N+n.val)] =ᵐ[gaussianSequentialMatrixLaw μ v a t]
      (fun x => ((N : ℝ)⁻¹ • dilationVarianceCoordinateL (𝕂 := 𝕂) i n.rev)
        ((gaussianSequentialMatrixLaw μ v a t)[
          (fun y => ‖gaussianMatrixTruncatedEntry μ v a t K R i n.val y‖^2) |
          rowMajorFiltration N N (i.val*N+n.val)] x)) := by
  let L := (N : ℝ)⁻¹ • dilationVarianceCoordinateL (𝕂 := 𝕂) i n.rev
  have hi := (gaussianMatrixTruncatedEntry_basics μ hX v a ha t K R hR i n.val).2.2.2
  rw [gaussianHermitianCoordinateSquare_eq]
  exact ⟨L.integrable_comp hi, (L.comp_condExp_comm hi).symm⟩

#print axioms gaussianHermitianCoordinateSquare_condExp
end SpectralRadiusUpperTail
