import SpectralRadiusUpperTail.RealSchurFiniteShape
import SpectralRadiusUpperTail.RealSchurMixedCodeClassImage

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Operator

/-- Finite shape, finite index reordering, and finite spectral code.
Retaining all reorderings avoids imposing an arbitrary canonical one. -/
abbrev RealSchurFiniteCode (n : ℕ) :=
  Σ S : RealSchurFiniteShape n,
    (Fin n ≃ RealSchurMixedCoord S.sizes) ×
      (Fin S.blockCount → Fin (Fintype.card (RealSchurMixedCoord S.sizes)) → Bool)

noncomputable instance (n : ℕ) : Fintype (RealSchurFiniteCode n) := by
  classical
  unfold RealSchurFiniteCode
  infer_instance

def realSchurFiniteCodeClass {n : ℕ} (I : RealSchurFiniteCode n) :
    Set (Matrix (Fin n) (Fin n) ℝ) :=
  (Matrix.reindex I.2.1 I.2.1) ⁻¹' realSchurMixedCodeClass I.1.sizes I.2.2

theorem realSchur_reindex_continuous
    {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ) :
    Continuous (Matrix.reindex e e : Matrix ι ι ℝ → Matrix κ κ ℝ) := by
  exact (Matrix.reindexLinearEquiv ℝ ℝ e e).continuous_of_finiteDimensional

theorem measurableSet_realSchurFiniteCodeClass
    {n : ℕ} (I : RealSchurFiniteCode n) :
    MeasurableSet (realSchurFiniteCodeClass I) :=
  (measurableSet_realSchurMixedCodeClass I.1.sizes I.1.sizes_pos I.2.2).preimage
    (realSchur_reindex_continuous I.2.1).measurable

/-- The fixed-coordinate finite classes are constant along any connected
continuous family with fixed simple characteristic polynomial. -/
theorem realSchurFiniteCodeClass_connected_iff
    {n : ℕ} (I : RealSchurFiniteCode n)
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    (f : X → Matrix (Fin n) (Fin n) ℝ) (hf : Continuous f)
    (hsep : ∀ x, (f x).charpoly.Separable)
    (hpoly : ∀ x y, (f x).charpoly=(f y).charpoly) (x y : X) :
    f x ∈ realSchurFiniteCodeClass I ↔ f y ∈ realSchurFiniteCodeClass I := by
  apply realSchurMixedCodeClass_connected_iff I.1.sizes I.1.sizes_small I.2.2
    (fun z => Matrix.reindex I.2.1 I.2.1 (f z))
  · exact (realSchur_reindex_continuous I.2.1).comp hf
  · intro z
    simpa only [Matrix.charpoly_reindex] using hsep z
  · intro z w
    simpa only [Matrix.charpoly_reindex] using hpoly z w

#print axioms realSchur_reindex_continuous
#print axioms measurableSet_realSchurFiniteCodeClass
#print axioms realSchurFiniteCodeClass_connected_iff
end SpectralRadiusUpperTail
