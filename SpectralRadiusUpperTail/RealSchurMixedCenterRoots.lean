import SpectralRadiusUpperTail.RealSchurMixedBlockRoots
import SpectralRadiusUpperTail.RealSchurMixedChartRootCounts
import SpectralRadiusUpperTail.RealSchurMixedChartSpectrum
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix BigOperators

/-- An admissible block-upper real-Schur center has precisely the named
real roots and nonreal conjugate pairs, with algebraic multiplicity. -/
theorem realSchurMixedChart_center_aroots
    {m : ℕ} (B : Fin m → RealSchurChartBlock)
    (T : Matrix (RealSchurMixedCoord (fun i => (B i).size))
      (RealSchurMixedCoord (fun i => (B i).size)) ℝ)
    (hT : ∀ a b : Fin m, b < a →
      ∀ x : Fin ((B a).size), ∀ y : Fin ((B b).size),
        T ⟨a,x⟩ ⟨b,y⟩ = 0)
    (hdiag : ∀ i a b, T ⟨i,a⟩ ⟨i,b⟩ = (B i).matrix a b) :
    T.charpoly.aroots ℂ =
      (Finset.univ : Finset (Fin m)).val.bind
        (fun i => (B i).complexRoots) := by
  rw [realSchurMixedChart_charpoly_product B T hT hdiag]
  simp only [Polynomial.aroots_def, Polynomial.map_prod]
  have hne : (∏ i : Fin m,
      ((B i).matrix.charpoly.map (algebraMap ℝ ℂ))) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact Polynomial.map_monic_ne_zero (Matrix.charpoly_monic (B i).matrix)
  rw [Polynomial.roots_prod _ _ hne]
  simp_rw [← Polynomial.aroots_def,
    RealSchurChartBlock.aroots_eq_complexRoots]

/-- The same exact root multiset holds after any orthogonal rotation of
the block-upper Schur center. -/
theorem realSchurMixedChart_rotated_center_aroots
    {m : ℕ} (B : Fin m → RealSchurChartBlock)
    (T : Matrix (RealSchurMixedCoord (fun i => (B i).size))
      (RealSchurMixedCoord (fun i => (B i).size)) ℝ)
    (hT : ∀ a b : Fin m, b < a →
      ∀ x : Fin ((B a).size), ∀ y : Fin ((B b).size),
        T ⟨a,x⟩ ⟨b,y⟩ = 0)
    (hdiag : ∀ i a b, T ⟨i,a⟩ ⟨i,b⟩ = (B i).matrix a b)
    (Q : Matrix (RealSchurMixedCoord (fun i => (B i).size))
      (RealSchurMixedCoord (fun i => (B i).size)) ℝ)
    (hQ : Qᵀ*Q=1) :
    (Q*T*Qᵀ).charpoly.aroots ℂ =
      (Finset.univ : Finset (Fin m)).val.bind
        (fun i => (B i).complexRoots) := by
  rw [realMatrixOrthogonalConjugation_charpoly _ Q T hQ]
  exact realSchurMixedChart_center_aroots B T hT hdiag

/-- Any root count of an orthogonal mixed-Schur center is the sum of
the corresponding named scalar and conjugate-pair block counts. -/
theorem realSchurMixedChart_rotated_center_countP
    {m : ℕ} (B : Fin m → RealSchurChartBlock)
    (T : Matrix (RealSchurMixedCoord (fun i => (B i).size))
      (RealSchurMixedCoord (fun i => (B i).size)) ℝ)
    (hT : ∀ a b : Fin m, b < a →
      ∀ x : Fin ((B a).size), ∀ y : Fin ((B b).size),
        T ⟨a,x⟩ ⟨b,y⟩ = 0)
    (hdiag : ∀ i a b, T ⟨i,a⟩ ⟨i,b⟩ = (B i).matrix a b)
    (Q : Matrix (RealSchurMixedCoord (fun i => (B i).size))
      (RealSchurMixedCoord (fun i => (B i).size)) ℝ)
    (hQ : Qᵀ*Q=1)
    (p : ℂ → Prop) [DecidablePred p] :
    Multiset.countP p ((Q*T*Qᵀ).charpoly.aroots ℂ) =
      ∑ i : Fin m, Multiset.countP p (B i).complexRoots := by
  rw [realSchurMixedChart_rotated_center_aroots B T hT hdiag Q hQ,
    realSchurMixed_countP_bind]
  rfl

#print axioms realSchurMixedChart_center_aroots
#print axioms realSchurMixedChart_rotated_center_countP
end SpectralRadiusUpperTail
