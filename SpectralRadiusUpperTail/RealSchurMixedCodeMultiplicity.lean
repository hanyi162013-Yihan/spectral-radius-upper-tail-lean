import SpectralRadiusUpperTail.FiniteCoverIntegralNormalization
import SpectralRadiusUpperTail.RealSchurMixedCodeClassImage
import SpectralRadiusUpperTail.RealSchurMixedCodeClassFiber
import SpectralRadiusUpperTail.RealSchurMixedCodeClassOrthogonal

namespace SpectralRadiusUpperTail
open scoped ENNReal Matrix Matrix.Norms.Operator

/-- Number of realized ordered spectral codes for a fixed block shape. -/
noncomputable def realSchurMixedCodeMultiplicity
    {m : ℕ} (s : Fin m → ℕ)
    (A : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ) : ℝ≥0∞ :=
  finiteCoverMultiplicity (realSchurMixedCodeClass s) A

theorem realSchurMixedCodeMultiplicity_measurable
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i) :
    Measurable (realSchurMixedCodeMultiplicity s) :=
  finiteCoverMultiplicity_measurable _ (measurableSet_realSchurMixedCodeClass s hs)

theorem realSchurMixedCodeMultiplicity_ne_top
    {m : ℕ} (s : Fin m → ℕ)
    (A : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ) :
    realSchurMixedCodeMultiplicity s A ≠ ∞ :=
  finiteCoverMultiplicity_ne_top _ A

theorem realSchurMixedCodeMultiplicity_pos_of_upper
    {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hT : realSchurMixedLowerProjection s T=0) (hsep : T.charpoly.Separable) :
    0 < realSchurMixedCodeMultiplicity s T := by
  apply finiteCoverMultiplicity_pos
  apply Set.mem_iUnion_of_mem (realSchurMixedSpectralCode s T)
  exact ⟨⟨1,by simp⟩,T,hT,hsep,rfl,by simp⟩

theorem realSchurMixedCodeMultiplicity_orthogonal
    {m : ℕ} (s : Fin m → ℕ) (P : RealSchurMixedOrthogonalFrame s)
    (A : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ) :
    realSchurMixedCodeMultiplicity s (P.val*A*P.valᵀ)=realSchurMixedCodeMultiplicity s A := by
  classical
  apply Finset.sum_congr rfl
  intro code _
  simp only [Set.indicator_apply, realSchurMixedCodeClass_orthogonal_iff s code P A]

/-- The exact overlap count can be taken outside the strictly-upper
Gaussian integral. It may depend on diagonal spectra. -/
theorem realSchurMixedCodeMultiplicity_upper_fiber
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, s i=1 ∨ s i=2)
    (d : RealSchurMixedDiagonalEntry s → ℝ)
    (u v : RealSchurMixedStrictUpperEntry s → ℝ)
    (hsep : (realSchurMixedUpperEntryJoin s d u).charpoly.Separable) :
    realSchurMixedCodeMultiplicity s (realSchurMixedUpperEntryJoin s d u)=
      realSchurMixedCodeMultiplicity s (realSchurMixedUpperEntryJoin s d v) := by
  classical
  apply Finset.sum_congr rfl
  intro code _
  simp only [Set.indicator_apply, realSchurMixedCodeClass_upper_fiber_iff s hs code d u v hsep]

#print axioms realSchurMixedCodeMultiplicity_measurable
#print axioms realSchurMixedCodeMultiplicity_ne_top
#print axioms realSchurMixedCodeMultiplicity_pos_of_upper
#print axioms realSchurMixedCodeMultiplicity_orthogonal
#print axioms realSchurMixedCodeMultiplicity_upper_fiber
end SpectralRadiusUpperTail
