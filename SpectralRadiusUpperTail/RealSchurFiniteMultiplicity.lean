import SpectralRadiusUpperTail.RealSchurFiniteCodeCoverage
import SpectralRadiusUpperTail.FiniteCoverIntegralNormalization

namespace SpectralRadiusUpperTail
open scoped ENNReal Matrix Matrix.Norms.Operator

/-- Exact finite overlap count, now including every block shape and
entry reordering in the fixed matrix dimension. -/
noncomputable def realSchurFiniteMultiplicity (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ) : ℝ≥0∞ :=
  finiteCoverMultiplicity (fun I : RealSchurFiniteCode n => realSchurFiniteCodeClass I) A

theorem realSchurFiniteMultiplicity_measurable (n : ℕ) :
    Measurable (realSchurFiniteMultiplicity n) :=
  finiteCoverMultiplicity_measurable _ measurableSet_realSchurFiniteCodeClass

theorem realSchurFiniteMultiplicity_ne_top (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
    realSchurFiniteMultiplicity n A ≠ ∞ := finiteCoverMultiplicity_ne_top _ A

theorem realSchurFiniteMultiplicity_pos (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hsep : A.charpoly.Separable) : 0 < realSchurFiniteMultiplicity n A :=
  finiteCoverMultiplicity_pos _ A (realMatrix_mem_finiteSchurCodeUnion A hsep)

/-- The total overlap count, including different shapes, is constant
on connected continuous families with a fixed simple spectrum. -/
theorem realSchurFiniteMultiplicity_connected
    {n : ℕ} {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    (f : X → Matrix (Fin n) (Fin n) ℝ) (hf : Continuous f)
    (hsep : ∀ x, (f x).charpoly.Separable)
    (hpoly : ∀ x y, (f x).charpoly=(f y).charpoly) (x y : X) :
    realSchurFiniteMultiplicity n (f x)=realSchurFiniteMultiplicity n (f y) := by
  classical
  apply Finset.sum_congr rfl
  intro I _
  simp only [Set.indicator_apply,realSchurFiniteCodeClass_connected_iff I f hf hsep hpoly x y]

#print axioms realSchurFiniteMultiplicity_measurable
#print axioms realSchurFiniteMultiplicity_ne_top
#print axioms realSchurFiniteMultiplicity_pos
#print axioms realSchurFiniteMultiplicity_connected
end SpectralRadiusUpperTail
