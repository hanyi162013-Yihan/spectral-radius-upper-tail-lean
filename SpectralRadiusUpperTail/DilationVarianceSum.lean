import SpectralRadiusUpperTail.DiagonalVarianceMap
import Mathlib.Analysis.CStarAlgebra.Matrix

namespace SpectralRadiusUpperTail
open Matrix
open scoped BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] {N : ℕ}

/-- Both diagonal blocks of the actual coordinate-square sum, with the
column reversal dictated by the descending sequential coupling. -/
lemma dilationVarianceCoordinate_sum (w : Fin N → Fin N → ℝ) :
    (∑ i, ∑ n, dilationVarianceCoordinateL (𝕂 := 𝕂) i n.rev (w i n)) =
      Matrix.diagonal (fun p : Fin N ⊕ Fin N => match p with
        | Sum.inl i => ((∑ n, w i n : ℝ) : 𝕂)
        | Sum.inr j => ((∑ i, w i j.rev : ℝ) : 𝕂)) := by
  ext p q
  simp only [Finset.sum_apply, dilationVarianceCoordinateL_apply, Matrix.diagonal_apply]
  by_cases hpq : p=q
  · subst q
    simp only [if_pos rfl]
    cases p with
    | inl i => simp
    | inr j =>
      have he (n : Fin N) : j=n.rev ↔ n=j.rev := by
        rw [eq_comm, Fin.rev_eq_iff]
      simp [he]
  · simp [hpq]

lemma finite_average_le {B : ℝ} (hB : 0 ≤ B) (w : Fin N → ℝ)
    (hw : ∀ i, w i ≤ B) : (N : ℝ)⁻¹*(∑ i, w i) ≤ B := by
  have hs : ∑ i, w i ≤ (N : ℝ)*B := by
    simpa using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hw i)
  have hh := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr (Nat.cast_nonneg N))
  by_cases hN : N = 0
  · simpa [hN] using hB
  · have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
    simpa [← mul_assoc, hn] using hh

/-- Summing the two actual diagonal blocks gives a dimension-free operator
bound after normalization. This lemma assumes scalar coordinate bounds,
not the desired matrix variance bound. -/
theorem dilationVarianceCoordinate_sum_operator_le (w : Fin N → Fin N → ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hw0 : ∀ i n, 0 ≤ w i n) (hw : ∀ i n, w i n ≤ B) :
    ‖Matrix.toEuclideanCLM (n := Fin N ⊕ Fin N) (𝕜 := 𝕂)
      ((N : ℝ)⁻¹ • (∑ i, ∑ n, dilationVarianceCoordinateL (𝕂 := 𝕂) i n.rev (w i n)))‖ ≤ B := by
  rw [dilationVarianceCoordinate_sum]
  let u : Fin N ⊕ Fin N → 𝕂 := fun p => match p with
    | Sum.inl i => ((∑ n, w i n : ℝ) : 𝕂)
    | Sum.inr j => ((∑ i, w i j.rev : ℝ) : 𝕂)
  change ‖Matrix.toEuclideanCLM (n := Fin N ⊕ Fin N) (𝕜 := 𝕂)
    ((N : ℝ)⁻¹ • (Matrix.diagonal u : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) 𝕂))‖ ≤ B
  rw [← Matrix.diagonal_smul,
    Matrix.l2_opNorm_toEuclideanCLM, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg hB).mpr
  intro p
  have hrow0 (i : Fin N) : 0 ≤ (N : ℝ)⁻¹*(∑ n, w i n) := by
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N)) (Finset.sum_nonneg (fun n _ => hw0 i n))
  have hcol0 (j : Fin N) : 0 ≤ (N : ℝ)⁻¹*(∑ i, w i j.rev) := by
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N)) (Finset.sum_nonneg (fun i _ => hw0 i j.rev))
  cases p with
  | inl i =>
    change ‖(N : ℝ)⁻¹ • ((∑ n, w i n : ℝ) : 𝕂)‖ ≤ B
    rw [RCLike.real_smul_eq_coe_mul, ← RCLike.ofReal_mul, RCLike.norm_ofReal,
      abs_of_nonneg (hrow0 i)]
    exact finite_average_le hB _ (hw i)
  | inr j =>
    change ‖(N : ℝ)⁻¹ • ((∑ i, w i j.rev : ℝ) : 𝕂)‖ ≤ B
    rw [RCLike.real_smul_eq_coe_mul, ← RCLike.ofReal_mul, RCLike.norm_ofReal,
      abs_of_nonneg (hcol0 j)]
    exact finite_average_le hB _ (fun i => hw i j.rev)

#print axioms dilationVarianceCoordinate_sum_operator_le
end SpectralRadiusUpperTail
