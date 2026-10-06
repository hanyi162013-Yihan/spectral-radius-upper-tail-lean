import SpectralRadiusUpperTail.MatrixRootExteriorCounts
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

/-- The complete characteristic-root multiset of a real matrix is invariant
under complex conjugation, including algebraic multiplicities. -/
theorem realMatrix_charpoly_roots_conj {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    (((A.map Complex.ofRealHom).charpoly).roots.map (starRingEnd ℂ)) =
      ((A.map Complex.ofRealHom).charpoly).roots := by
  classical
  let C : Matrix (Fin n) (Fin n) ℂ := A.map Complex.ofRealHom
  have hC : C.map (starRingEnd ℂ) = C := by
    ext i j
    simp [C]
  have hchar : C.charpoly.map (starRingEnd ℂ) = C.charpoly := by
    rw [← Matrix.charpoly_map, hC]
  have hcard : C.charpoly.roots.card = C.charpoly.natDegree := by
    exact (IsAlgClosed.splits C.charpoly).natDegree_eq_card_roots.symm
  have hroots := C.charpoly_monic.roots_map_of_card_eq_natDegree
    (starRingEnd ℂ) hcard
  rw [hchar] at hroots
  exact hroots

#print axioms realMatrix_charpoly_roots_conj
end SpectralRadiusUpperTail
