import SpectralRadiusUpperTail.RealSchurMixedUpperEntryCoordinates
import Mathlib.MeasureTheory.Constructions.Pi

namespace SpectralRadiusUpperTail
open MeasureTheory

/-- Grouping a finite real array into dependent finite blocks preserves
the product Lebesgue measure. -/
theorem real_array_sigmaCurry_measurePreserving
    {ι : Type*} [Fintype ι] (κ : ι → Type*) [∀ i, Fintype (κ i)] :
    MeasurePreserving (MeasurableEquiv.piCurry (fun (i : ι) (_ : κ i) => ℝ)) := by
  let E := MeasurableEquiv.piCurry (fun (i : ι) (_ : κ i) => ℝ)
  have h : MeasurePreserving E.symm := by
    refine ⟨E.symm.measurable,?_⟩
    apply Eq.symm
    apply Measure.pi_eq
    intro S hS
    rw [E.symm.map_apply]
    have heq : E.symm ⁻¹' Set.pi Set.univ S =
        Set.pi Set.univ (fun i => Set.pi Set.univ (fun j => S ⟨i,j⟩)) := by
      ext f
      simp [E,Set.mem_pi,Sigma.forall,Sigma.uncurry]
    rw [heq,volume_pi_pi]
    simp only [volume_pi_pi]
    exact (Fintype.prod_sigma (fun p : Sigma κ => (volume : Measure ℝ) (S p))).symm
  exact h.symm

def realSchurMixedDiagonalIndexEquiv {m : ℕ} (s : Fin m → ℕ) :
    (Σ i : Fin m, Fin (s i) × Fin (s i)) ≃ RealSchurMixedDiagonalEntry s where
  toFun p := ⟨(⟨p.1,p.2.1⟩,⟨p.1,p.2.2⟩),rfl⟩
  invFun z := by
    rcases z with ⟨⟨⟨i,a⟩,⟨j,b⟩⟩,h⟩
    dsimp only at h
    subst j
    exact ⟨i,(a,b)⟩
  left_inv p := by rcases p with ⟨i,a,b⟩; rfl
  right_inv z := by
    rcases z with ⟨⟨⟨i,a⟩,⟨j,b⟩⟩,h⟩
    dsimp only at h
    subst j
    rfl

/-- The diagonal-entry coordinates are exactly the independent arrays
of entries of the native diagonal blocks. -/
noncomputable def realSchurMixedDiagonalProductEquiv {m : ℕ} (s : Fin m → ℕ) :
    (RealSchurMixedDiagonalEntry s → ℝ) ≃ᵐ
      ((i : Fin m) → (Fin (s i) × Fin (s i)) → ℝ) :=
  ((MeasurableEquiv.piCongrLeft (fun _ : RealSchurMixedDiagonalEntry s => ℝ)
    (realSchurMixedDiagonalIndexEquiv s)).symm).trans
      (MeasurableEquiv.piCurry (fun (i : Fin m) (_ : Fin (s i) × Fin (s i)) => ℝ))

theorem realSchurMixedDiagonalProductEquiv_apply {m : ℕ} (s : Fin m → ℕ)
    (d : RealSchurMixedDiagonalEntry s → ℝ) (i : Fin m) (a b : Fin (s i)) :
    realSchurMixedDiagonalProductEquiv s d i (a,b)=d ⟨(⟨i,a⟩,⟨i,b⟩),rfl⟩ := rfl

theorem realSchurMixedDiagonalProductEquiv_measurePreserving
    {m : ℕ} (s : Fin m → ℕ) :
    MeasurePreserving (realSchurMixedDiagonalProductEquiv s) :=
  (real_array_sigmaCurry_measurePreserving (fun i : Fin m => Fin (s i) × Fin (s i))).comp
    (volume_measurePreserving_piCongrLeft
      (fun _ : RealSchurMixedDiagonalEntry s => ℝ) (realSchurMixedDiagonalIndexEquiv s)).symm

#print axioms real_array_sigmaCurry_measurePreserving
#print axioms realSchurMixedDiagonalIndexEquiv
#print axioms realSchurMixedDiagonalProductEquiv_measurePreserving
end SpectralRadiusUpperTail
