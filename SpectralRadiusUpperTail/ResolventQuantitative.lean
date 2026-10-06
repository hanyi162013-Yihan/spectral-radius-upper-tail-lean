import SpectralRadiusUpperTail.ResolventPerturbation
import Mathlib.Tactic.Linarith

namespace SpectralRadiusUpperTail

/-- Quantitative Neumann stability using the actual resolvent and no normality assumption. -/
lemma resolvent_add_quantitative {𝕂 R : Type*} [CommRing 𝕂]
    [NormedRing R] [CompleteSpace R] [Algebra 𝕂 R]
    (a e : R) (z : 𝕂) (M : ℝ) (hM : 0 ≤ M)
    (hz : z ∈ resolventSet 𝕂 a) (hbase : ‖resolvent a z‖ ≤ M)
    (hsmall : M*‖e‖ ≤ 1/2) :
    z ∈ resolventSet 𝕂 (a+e) ∧ ‖resolvent (a+e) z‖ ≤ 2*M ∧
      ‖resolvent (a+e) z-resolvent a z‖ ≤ 2*M^2*‖e‖ := by
  have hp : ‖Ring.inverse (algebraMap 𝕂 R z-a)‖*‖e‖ < 1 := by
    change ‖resolvent a z‖*‖e‖ < 1
    have hh := mul_le_mul_of_nonneg_right hbase (norm_nonneg e)
    linarith
  have hz' := mem_resolventSet_add_of_norm a e z hz hp
  have hd : ‖resolvent (a+e) z-resolvent a z‖ ≤
      (‖resolvent (a+e) z‖*‖e‖)*M := by
    rw [spectrum.resolvent_sub_resolvent hz' hz, add_sub_cancel_left]
    exact (norm_mul_le _ _).trans (mul_le_mul (norm_mul_le _ _) hbase
      (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
  have ht := norm_add_le (resolvent (a+e) z-resolvent a z) (resolvent a z)
  rw [sub_add_cancel] at ht
  have hc := mul_le_mul_of_nonneg_left hsmall (norm_nonneg (resolvent (a+e) z))
  have hb : ‖resolvent (a+e) z‖ ≤ 2*M := by nlinarith
  refine ⟨hz', hb, ?_⟩
  have hh := mul_le_mul_of_nonneg_right hb (mul_nonneg (norm_nonneg e) hM)
  nlinarith

#print axioms resolvent_add_quantitative
end SpectralRadiusUpperTail
