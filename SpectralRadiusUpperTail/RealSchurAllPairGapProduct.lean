import SpectralRadiusUpperTail.RealSchurAllPairOrbitDeterminant
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

/-- For an all-pair real Schur chart, the complete angular derivative has
the product of the two spectral-gap factors for every pair of conjugate
blocks. This statement is still local to the chart; no global change of
variables or eigenvalue density is inferred from it. -/
theorem realSchurAllPairOrbitMatrix_gap_product {m : ℕ}
    (T : Matrix (Fin m) (Fin m) (Matrix (Fin 2) (Fin 2) ℝ))
    (hT : ∀ a b : Fin m, b < a → T a b = 0)
    (x b c y : Fin m → ℝ)
    (hdiag : ∀ i, T i i = realSchurBlock (x i) (b i) (c i))
    (hbc : ∀ i, b i*c i = (y i)^2) :
    (realSchurAllPairOrbitMatrix T).det =
      ∏ p : RealSchurLowerIndex m,
        (((x p.1.1-x p.1.2)^2+(y p.1.1-y p.1.2)^2)*
          ((x p.1.1-x p.1.2)^2+(y p.1.1+y p.1.2)^2)) := by
  rw [realSchurAllPairOrbitMatrix_det T hT x b c hdiag]
  apply Finset.prod_congr rfl
  intro p _
  exact realSchur_pair_pair_factor
    (x p.1.1) (b p.1.1) (c p.1.1)
    (x p.1.2) (b p.1.2) (c p.1.2)
    (y p.1.1) (y p.1.2)
    (hbc p.1.1) (hbc p.1.2)

#print axioms realSchurAllPairOrbitMatrix_gap_product
end SpectralRadiusUpperTail
