import SpectralRadiusUpperTail.MarkedRealEigenlineBasis
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix BigOperators

/-- Scalar and complementary vector coordinates in the existing marked
two-block index type. -/
def markedRealVectorCons (m : ℕ) (a : ℝ) (u : Fin m → ℝ) :
    RealSchurMixedCoord (markedRealTwoBlockSizes m) → ℝ :=
  fun i => if h : i.1 = 0 then a else
    u (Fin.cast (by change (if i.1 = 0 then 1 else m) = m; exact if_neg h) i.2)

theorem markedRealVectorCons_first (m : ℕ) (a : ℝ) (u : Fin m → ℝ) :
    markedRealVectorCons m a u (markedRealFirstCoordinate m) = a := by
  simp [markedRealVectorCons, markedRealFirstCoordinate]

theorem markedRealVectorCons_complement (m : ℕ) (a : ℝ) (u : Fin m → ℝ) (i : Fin m) :
    markedRealVectorCons m a u ⟨1,i⟩ = u i := by
  simp [markedRealVectorCons]

theorem markedRealVectorCons_sum (m : ℕ) (a : ℝ) (u : Fin m → ℝ) (f : ℝ → ℝ) :
    (∑ i, f (markedRealVectorCons m a u i)) = f a + ∑ i, f (u i) := by
  simp [Fintype.sum_sigma, Fin.sum_univ_two, markedRealTwoBlockSizes,
    markedRealVectorCons]

theorem markedRealVectorCons_dot (m : ℕ) (a b : ℝ) (u v : Fin m → ℝ) :
    markedRealVectorCons m a u ⬝ᵥ markedRealVectorCons m b v = a*b + u ⬝ᵥ v := by
  simp [dotProduct, Fintype.sum_sigma, Fin.sum_univ_two,
    markedRealTwoBlockSizes, markedRealVectorCons]

theorem markedRealVectorCons_ext (m : ℕ)
    (v w : RealSchurMixedCoord (markedRealTwoBlockSizes m) → ℝ)
    (hfirst : v (markedRealFirstCoordinate m) = w (markedRealFirstCoordinate m))
    (hcomp : ∀ i : Fin m, v ⟨1,i⟩ = w ⟨1,i⟩) : v = w := by
  funext i
  rcases i with ⟨i,j⟩
  fin_cases i
  · have hj : j = markedRealZeroCoordinate m := by
      apply Fin.ext
      have hjlt : j.val < 1 := by simpa [markedRealTwoBlockSizes] using j.isLt
      dsimp [markedRealZeroCoordinate]
      omega
    subst j
    exact hfirst
  · exact hcomp j

#print axioms markedRealVectorCons_first
#print axioms markedRealVectorCons_complement
#print axioms markedRealVectorCons_sum
#print axioms markedRealVectorCons_dot
#print axioms markedRealVectorCons_ext
end SpectralRadiusUpperTail
