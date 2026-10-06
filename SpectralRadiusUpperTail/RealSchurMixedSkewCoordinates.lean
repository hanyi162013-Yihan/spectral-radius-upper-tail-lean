import SpectralRadiusUpperTail.RealSchurMixedUpperAlgebra
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

theorem realSchurMixedSkewEmbed_eq_transpose_sub
    {m : ℕ} (s : Fin m → ℕ)
    (ω : RealSchurMixedOrbitIndex s → ℝ) :
    realSchurMixedSkewEmbed s ω =
      (realSchurMixedLowerEmbed s ω)ᵀ - realSchurMixedLowerEmbed s ω := by
  classical
  unfold realSchurMixedSkewEmbed realSchurMixedLowerEmbed
  rw [Matrix.transpose_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q _
  ext a b
  simp only [realSchurMixedOrbitGenerator, Matrix.transpose_smul,
    Matrix.transpose_single, realSchurMixedLowerRow, realSchurMixedLowerCol,
    Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply]
  simp only [Matrix.single_apply, smul_eq_mul]
  split_ifs <;> ring

theorem realSchurMixedLowerProjection_transpose_lowerEmbed
    {m : ℕ} (s : Fin m → ℕ)
    (ω : RealSchurMixedOrbitIndex s → ℝ) :
    realSchurMixedLowerProjection s (realSchurMixedLowerEmbed s ω)ᵀ = 0 := by
  classical
  funext p
  change ((realSchurMixedLowerEmbed s ω)ᵀ)
    (realSchurMixedLowerRow s p) (realSchurMixedLowerCol s p) = 0
  simp only [realSchurMixedLowerEmbed,
    Matrix.sum_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro q _
  have hne : ¬ (realSchurMixedLowerRow s q = realSchurMixedLowerCol s p ∧
      realSchurMixedLowerCol s q = realSchurMixedLowerRow s p) := by
    rintro ⟨hr,hc⟩
    have hp : (realSchurMixedLowerCol s p).1 <
        (realSchurMixedLowerRow s p).1 := p.1.2
    have hq : (realSchurMixedLowerCol s q).1 <
        (realSchurMixedLowerRow s q).1 := q.1.2
    simp only [← hr, ← hc] at hp
    exact (lt_asymm hp hq)
  rw [Matrix.single_apply_of_ne _ _ _ _ _ hne, mul_zero]

theorem realSchurMixedLowerProjection_skewEmbed
    {m : ℕ} (s : Fin m → ℕ)
    (ω : RealSchurMixedOrbitIndex s → ℝ) :
    realSchurMixedLowerProjection s (realSchurMixedSkewEmbed s ω) = -ω := by
  rw [realSchurMixedSkewEmbed_eq_transpose_sub, map_sub,
    realSchurMixedLowerProjection_transpose_lowerEmbed,
    realSchurMixedLowerProjection_embed]
  exact zero_sub ω

#print axioms realSchurMixedLowerProjection_skewEmbed
end SpectralRadiusUpperTail
