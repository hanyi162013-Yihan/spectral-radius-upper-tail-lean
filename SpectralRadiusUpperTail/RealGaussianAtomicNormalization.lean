import SpectralRadiusUpperTail.RealSchurFiniteAtomicClass
import SpectralRadiusUpperTail.RealSchurFixedFlagFiber
import SpectralRadiusUpperTail.RealGaussianActualSimpleSpectrum
import SpectralRadiusUpperTail.FiniteCoverIntegralNormalization

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix Matrix.Norms.Operator

/-- Exact finite overlap count restricted to scalar/nonreal-pair blocks, including every shape and
entry reordering in the fixed matrix dimension. -/
noncomputable def realSchurAtomicMultiplicity (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ) : ℝ≥0∞ :=
  finiteCoverMultiplicity (fun I : RealSchurFiniteCode n => realSchurFiniteAtomicClass I) A

theorem realSchurAtomicMultiplicity_measurable (n : ℕ) :
    Measurable (realSchurAtomicMultiplicity n) :=
  finiteCoverMultiplicity_measurable _ measurableSet_realSchurFiniteAtomicClass

theorem realSchurAtomicMultiplicity_ne_top (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
    realSchurAtomicMultiplicity n A ≠ ∞ := finiteCoverMultiplicity_ne_top _ A

theorem realSchurAtomicMultiplicity_pos (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hsep : A.charpoly.Separable) : 0 < realSchurAtomicMultiplicity n A :=
  finiteCoverMultiplicity_pos _ A (realMatrix_mem_finiteAtomicSchurUnion A hsep)

/-- The total overlap count, including different shapes, is constant
on connected continuous families with a fixed simple spectrum. -/
theorem realSchurAtomicMultiplicity_connected
    {n : ℕ} {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    (f : X → Matrix (Fin n) (Fin n) ℝ) (hf : Continuous f)
    (hsep : ∀ x, (f x).charpoly.Separable)
    (hpoly : ∀ x y, (f x).charpoly=(f y).charpoly) (x y : X) :
    realSchurAtomicMultiplicity n (f x)=realSchurAtomicMultiplicity n (f y) := by
  classical
  apply Finset.sum_congr rfl
  intro I _
  simp only [Set.indicator_apply,realSchurFiniteAtomicClass_connected_iff I f hf hsep hpoly x y]

/-- The total multiplicity, including every shape, is constant along
each full angular/strict-upper fiber. This is the normalization needed
before integrating its independent Gaussian entries. -/
theorem realSchurAtomicMultiplicity_flag_fiber
    {n m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (e : Fin n ≃ RealSchurMixedCoord s) (Q : RealSchurMixedOrthogonalFrame s)
    (d : RealSchurMixedDiagonalEntry s → ℝ)
    (hsep : (realSchurMixedUpperEntryJoin s d 0).charpoly.Separable)
    (z w : (RealSchurMixedOrbitIndex s → ℝ) × (RealSchurMixedStrictUpperEntry s → ℝ)) :
    realSchurAtomicMultiplicity n (realSchurFixedFlagFiberMatrix s e Q d z) =
      realSchurAtomicMultiplicity n (realSchurFixedFlagFiberMatrix s e Q d w) := by
  apply realSchurAtomicMultiplicity_connected _ (realSchurFixedFlagFiberMatrix_continuous s e Q d)
  · intro v
    rw [realSchurFixedFlagFiberMatrix_charpoly s hs]
    exact hsep
  · intro v t
    rw [realSchurFixedFlagFiberMatrix_charpoly s hs,realSchurFixedFlagFiberMatrix_charpoly s hs]

/-- Exact finite-cover normalization for the actual iid real Gaussian
matrix law. Every shape, index reordering, and code is included, while
the reciprocal total multiplicity counts each sampled matrix only once. -/
theorem realGaussian_lintegral_finiteAtomic_normalized
    (n : ℕ) (g : ((Fin n × Fin n) → ℝ) → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ x, g x ∂gaussianMatrixLaw n) =
      ∑ I : RealSchurFiniteCode n,
        ∫⁻ x in {x | Matrix.of x.curry ∈ realSchurFiniteAtomicClass I},
          (realSchurAtomicMultiplicity n (Matrix.of x.curry))⁻¹*g x ∂gaussianMatrixLaw n := by
  classical
  let S := fun I : RealSchurFiniteCode n =>
    {x : (Fin n × Fin n) → ℝ | Matrix.of x.curry ∈ realSchurFiniteAtomicClass I}
  have hC : Continuous (fun x : (Fin n × Fin n) → ℝ => Matrix.of x.curry) := by
    apply continuous_matrix
    intro i j
    exact continuous_apply (i,j)
  have hS : ∀ I, MeasurableSet (S I) := fun I =>
    (measurableSet_realSchurFiniteAtomicClass I).preimage hC.measurable
  have hM (x : (Fin n × Fin n) → ℝ) :
      finiteCoverMultiplicity S x=realSchurAtomicMultiplicity n (Matrix.of x.curry) := rfl
  have h := lintegral_finiteCover_normalized S hS (gaussianMatrixLaw n) g hg
  have hfull : ∀ᵐ x ∂gaussianMatrixLaw n, x ∈ ⋃ I, S I := by
    filter_upwards [realGaussianMatrix_charpoly_separable_ae n] with x hx
    obtain ⟨I,hI⟩ := Set.mem_iUnion.mp (realMatrix_mem_finiteAtomicSchurUnion (Matrix.of x.curry) hx)
    exact Set.mem_iUnion_of_mem I hI
  rw [Measure.restrict_eq_self_of_ae_mem hfull] at h
  simpa only [hM] using h.symm


#print axioms realSchurAtomicMultiplicity_measurable
#print axioms realSchurAtomicMultiplicity_ne_top
#print axioms realSchurAtomicMultiplicity_pos
#print axioms realSchurAtomicMultiplicity_connected
#print axioms realSchurAtomicMultiplicity_flag_fiber
#print axioms realGaussian_lintegral_finiteAtomic_normalized
end SpectralRadiusUpperTail
