import SpectralRadiusUpperTail.MatrixExteriorRootPower
import SpectralRadiusUpperTail.OutlierSpectralRadius
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix.Norms.Frobenius

/-- A deterministic polynomial-moment envelope for the full exterior
characteristic-root power sum. It includes the zero-power case. -/
theorem matrixExteriorRootPower_le_dim_frobeniusPower
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) :
    matrixExteriorRootPower A k ≤
      (n : ℝ)*(1+‖A^k‖^2) := by
  classical
  let w : ℂ → ℝ := fun z =>
    if 1 < ‖z‖ then ‖z‖^(2*k) else 0
  have hcard : A.charpoly.roots.card = n := by
    rw [← (IsAlgClosed.splits A.charpoly).natDegree_eq_card_roots,
      Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hw (z : ℂ) (hz : z ∈ A.charpoly.roots) :
      w z ≤ 1+‖A^k‖^2 := by
    by_cases hk : k = 0
    · subst k
      dsimp [w]
      split_ifs <;> nlinarith [sq_nonneg (‖A^0‖)]
    · by_cases houter : 1 < ‖z‖
      · have hspec : z ∈ spectrum ℂ A :=
          Matrix.mem_spectrum_of_isRoot_charpoly
            ((Polynomial.mem_roots A.charpoly_monic.ne_zero).mp hz)
        have hrad := complex_eigenvalue_le_spectralRadius A z hspec
        have hpow := pow_le_pow_left₀ (norm_nonneg z) hrad k
        have hfrob := complex_spectralRadius_power_le_frobenius A k hk
        have hsq := pow_le_pow_left₀
          (pow_nonneg (norm_nonneg z) k) (hpow.trans hfrob) 2
        dsimp [w]
        rw [if_pos houter]
        have heq : ‖z‖^(2*k) = (‖z‖^k)^2 := by ring
        rw [heq]
        linarith
      · simp [w, houter]
        nlinarith [sq_nonneg (‖A^k‖)]
  have hsum := Multiset.sum_map_le_sum_map (s := A.charpoly.roots)
    w (fun _ => 1+‖A^k‖^2) hw
  simpa [matrixExteriorRootPower, w, Multiset.map_const,
    hcard, nsmul_eq_mul, mul_add] using hsum

#print axioms matrixExteriorRootPower_le_dim_frobeniusPower
end SpectralRadiusUpperTail
