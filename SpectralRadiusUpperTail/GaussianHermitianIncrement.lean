import SpectralRadiusUpperTail.GaussianMatrixMartingale
import SpectralRadiusUpperTail.DiagonalVarianceMap

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped MeasureTheory
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂] {N : ℕ}

/-- Actual normalized Hermitian increments, with the same fixed law and
filtration as the original matrix martingale. -/
noncomputable def gaussianHermitianCoordinateIncrement (μ : Measure 𝕂) [SFinite μ]
    (v : ℕ → 𝕂) (a : ℝ) (t : Fin N → 𝕂) (K R : ℝ) (i n : Fin N) :
    (Fin N → Fin N → 𝕂 × 𝕂) → ((Fin N ⊕ Fin N) → (Fin N ⊕ Fin N) → 𝕂) :=
  hermitianDilationL ∘ gaussianMatrixCoordinateIncrement μ v a t K R i n

theorem gaussianHermitianCoordinateIncrement_basics (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (v : ℕ → 𝕂) (a : ℝ) (ha : 0 < a)
    (t : Fin N → 𝕂) (K R : ℝ) (hR : 0 ≤ R) (i n : Fin N) :
    Integrable (gaussianHermitianCoordinateIncrement μ v a t K R i n)
        (gaussianSequentialMatrixLaw μ v a t) ∧
      StronglyMeasurable[rowMajorFiltration N N (i.val*N+n.val+1)]
        (gaussianHermitianCoordinateIncrement μ v a t K R i n) ∧
      (gaussianSequentialMatrixLaw μ v a t)[gaussianHermitianCoordinateIncrement μ v a t K R i n |
        rowMajorFiltration N N (i.val*N+n.val)] =ᵐ[gaussianSequentialMatrixLaw μ v a t] 0 := by
  have hb := gaussianMatrixCoordinateIncrement_basics μ hX v a ha t K R hR i n
  let L : (Fin N → Fin N → 𝕂) →L[ℝ] ((Fin N ⊕ Fin N) → (Fin N ⊕ Fin N) → 𝕂) :=
    hermitianDilationL
  unfold gaussianHermitianCoordinateIncrement
  exact ⟨L.integrable_comp hb.1, L.continuous.comp_stronglyMeasurable hb.2.1,
    condExp_continuousLinear_zero _ _ _ hb.1 hb.2.2 L⟩

lemma gaussianHermitianCoordinateIncrement_isHermitian (μ : Measure 𝕂) [SFinite μ]
    (v : ℕ → 𝕂) (a : ℝ) (t : Fin N → 𝕂) (K R : ℝ) (i n : Fin N)
    (x : Fin N → Fin N → 𝕂 × 𝕂) :
    Matrix.IsHermitian (gaussianHermitianCoordinateIncrement μ v a t K R i n x) := by
  change Matrix.IsHermitian (hermitianDilationL _)
  rw [hermitianDilationL_apply]
  exact hermitianDilation_isHermitian _

/-- An actual self-adjoint matrix-valued martingale, rather than an
assumed concentration interface. -/
theorem gaussianHermitianMatrix_martingale (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (v : ℕ → 𝕂) (a : ℝ) (ha : 0 < a)
    (t : Fin N → 𝕂) (K R : ℝ) (hR : 0 ≤ R) :
    Martingale (incrementPartialSum
      (finiteArrayIncrement (gaussianHermitianCoordinateIncrement μ v a t K R)))
      (rowMajorFiltration N N) (gaussianSequentialMatrixLaw μ v a t) := by
  have : IsProbabilityMeasure (gaussianSequentialMatrixLaw μ v a t) :=
    gaussianSequentialMatrixLaw_probability μ v a ha t
  have hb := gaussianHermitianCoordinateIncrement_basics μ hX v a ha t K R hR
  exact martingale_finiteArrayIncrement _ _ _ (fun i n => (hb i n).2.1)
    (fun i n => (hb i n).1) (fun i n => (hb i n).2.2)

#print axioms gaussianHermitianMatrix_martingale
end SpectralRadiusUpperTail
