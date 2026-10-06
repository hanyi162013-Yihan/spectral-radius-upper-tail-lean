import SpectralRadiusUpperTail.GaussianMatrixTruncation
import SpectralRadiusUpperTail.FiniteArrayMartingale
import SpectralRadiusUpperTail.MatrixCoordinateMap

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped MeasureTheory
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂] {N : ℕ}

/-- The actual normalized matrix-unit difference at row i and within-row
time n. The original column is n.rev, matching the descending row coupling. -/
noncomputable def gaussianMatrixCoordinateIncrement (μ : Measure 𝕂) [SFinite μ]
    (v : ℕ → 𝕂) (a : ℝ) (t : Fin N → 𝕂) (K R : ℝ) (i n : Fin N) :
    (Fin N → Fin N → 𝕂 × 𝕂) → (Fin N → Fin N → 𝕂) :=
  ((Real.sqrt (N : ℝ))⁻¹ • matrixCoordinateL (𝕂 := 𝕂) i n.rev) ∘
    gaussianMatrixTruncatedEntry μ v a t K R i n.val

theorem gaussianMatrixCoordinateIncrement_basics (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (v : ℕ → 𝕂) (a : ℝ) (ha : 0 < a)
    (t : Fin N → 𝕂) (K R : ℝ) (hR : 0 ≤ R) (i n : Fin N) :
    Integrable (gaussianMatrixCoordinateIncrement μ v a t K R i n)
        (gaussianSequentialMatrixLaw μ v a t) ∧
      StronglyMeasurable[rowMajorFiltration N N (i.val*N+n.val+1)]
        (gaussianMatrixCoordinateIncrement μ v a t K R i n) ∧
      (gaussianSequentialMatrixLaw μ v a t)[gaussianMatrixCoordinateIncrement μ v a t K R i n |
        rowMajorFiltration N N (i.val*N+n.val)] =ᵐ[gaussianSequentialMatrixLaw μ v a t] 0 := by
  let L : 𝕂 →L[ℝ] (Fin N → Fin N → 𝕂) := (Real.sqrt (N : ℝ))⁻¹ • matrixCoordinateL i n.rev
  have hb := gaussianMatrixTruncatedEntry_basics μ hX v a ha t K R hR i n.val
  exact ⟨L.integrable_comp hb.1, L.continuous.comp_stronglyMeasurable hb.2.2.1.stronglyMeasurable,
    condExp_continuousLinear_zero _ _ _ hb.1 hb.2.1 L⟩

/-- An actual normalized matrix-valued martingale on the fixed coupled matrix
law, with a single row-major filtration and zero continuation beyond N squared. -/
theorem gaussianTruncatedMatrix_martingale (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (v : ℕ → 𝕂) (a : ℝ) (ha : 0 < a)
    (t : Fin N → 𝕂) (K R : ℝ) (hR : 0 ≤ R) :
    Martingale (incrementPartialSum
      (finiteArrayIncrement (gaussianMatrixCoordinateIncrement μ v a t K R)))
      (rowMajorFiltration N N) (gaussianSequentialMatrixLaw μ v a t) := by
  have : IsProbabilityMeasure (gaussianSequentialMatrixLaw μ v a t) :=
    gaussianSequentialMatrixLaw_probability μ v a ha t
  have hb := gaussianMatrixCoordinateIncrement_basics μ hX v a ha t K R hR
  exact martingale_finiteArrayIncrement _ _ _ (fun i n => (hb i n).2.1)
    (fun i n => (hb i n).1) (fun i n => (hb i n).2.2)

#print axioms gaussianMatrixCoordinateIncrement_basics
#print axioms gaussianTruncatedMatrix_martingale
end SpectralRadiusUpperTail
