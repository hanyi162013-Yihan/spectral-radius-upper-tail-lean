import SpectralRadiusUpperTail.GaussianMatrixTruncationError
import SpectralRadiusUpperTail.GaussianStoppedErrorBound

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators Matrix.Norms.Frobenius
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂] {N : ℕ}

/-- Integrating the actual discarded entries gives the normalized matrix
second-moment bound on the constructed coupling, including dimension zero. -/
theorem gaussianMatrixTruncationError_secondMoment_le
    (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (hm : (∫ x : 𝕂, x ∂μ) = 0)
    (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1) (v : ℕ → 𝕂)
    (hv : ∑ j : Fin N, ‖v j.val‖^2 ≤ 1) (a d : ℝ) (ha : 0 < a) (hd : 0 < d)
    (hexp : Integrable (fun x : 𝕂 => Real.exp (4*d*‖x‖^2)) μ)
    (t : Fin N → 𝕂) (K δ R : ℝ) (hK : 0 ≤ K) (hδ : δ ≤ 1) (hR : 0 ≤ R)
    (hb : ∀ j : Fin N, ‖v j.val‖ ≤ δ)
    (hunit : gaussianTruncationScale μ a d K*δ ≤ 1)
    (herror : (gaussianTruncationScale μ a d K*δ)*gaussianLocalMomentCost μ d ≤ 1/2) :
    Integrable (fun x => ‖gaussianMatrixTruncationError μ v a t K R x‖^2)
      (gaussianSequentialMatrixLaw μ v a t) ∧
      (∫ x, ‖gaussianMatrixTruncationError μ v a t K R x‖^2
        ∂gaussianSequentialMatrixLaw μ v a t) ≤ (N : ℝ)*gaussianTruncationTail μ d R := by
  have (i : Fin N) : IsProbabilityMeasure (gaussianSequentialRowLaw μ v a N (t i) N) :=
    gaussianSequentialRowLaw_probability μ v a ha N (t i) N
  have hrow (i j : Fin N) := gaussianStoppedTruncationError_secondMoment_le
    μ hX hm hvar v N hv a d ha hd hexp (t i) (N-(j.val+1)) (by omega)
    K δ R hK hδ hR (by
      have he : N-(N-(j.val+1)+1) = j.val := by omega
      rw [he]
      exact hb j) hunit herror
  have hi (i j : Fin N) : Integrable (fun x : Fin N → Fin N → 𝕂 × 𝕂 =>
      ‖gaussianStoppedTruncationError μ v a N (t i) K R (N-(j.val+1)) (x i)‖^2)
      (gaussianSequentialMatrixLaw μ v a t) := by
    convert! (measurePreserving_eval
      (fun k : Fin N => gaussianSequentialRowLaw μ v a N (t k) N) i).integrable_comp_of_integrable
      (hrow i j).1 using 1
  have hentry (i j : Fin N) :
      (∫ x, ‖gaussianStoppedTruncationError μ v a N (t i) K R (N-(j.val+1)) (x i)‖^2
        ∂gaussianSequentialMatrixLaw μ v a t) ≤ gaussianTruncationTail μ d R := by
    have hmarg := gaussianSequentialMatrixLaw_row μ v a ha t i
    have hg : AEStronglyMeasurable (fun x =>
        ‖gaussianStoppedTruncationError μ v a N (t i) K R (N-(j.val+1)) x‖^2)
        ((gaussianSequentialMatrixLaw μ v a t).map (fun x => x i)) := by
      rw [hmarg]
      exact (hrow i j).1.aestronglyMeasurable
    have he := integral_map (μ := gaussianSequentialMatrixLaw μ v a t)
      (measurable_pi_apply i).aemeasurable hg
    rw [hmarg] at he
    rw [← he]
    exact (hrow i j).2
  have hisum (i : Fin N) := integrable_finsetSum Finset.univ (fun j _ => hi i j)
  simp_rw [gaussianMatrixTruncationError_norm_sq]
  refine ⟨(integrable_finsetSum Finset.univ (fun i _ => hisum i)).const_mul _, ?_⟩
  rw [integral_const_mul, integral_finsetSum _ (fun i _ => hisum i)]
  simp_rw [integral_finsetSum _ (fun j _ => hi _ j)]
  calc
    _ ≤ (1/(N : ℝ))*(∑ _i : Fin N, ∑ _j : Fin N, gaussianTruncationTail μ d R) :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hentry i j))) (by positivity)
    _ = (N : ℝ)*gaussianTruncationTail μ d R := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      by_cases hN : N = 0
      · simp [hN]
      · have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
        field_simp

#print axioms gaussianMatrixTruncationError_secondMoment_le
end SpectralRadiusUpperTail
