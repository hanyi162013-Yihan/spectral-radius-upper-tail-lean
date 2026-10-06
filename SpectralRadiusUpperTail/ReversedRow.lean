import SpectralRadiusUpperTail.FiniteRevealedRow
import SpectralRadiusUpperTail.TailDenominator
import Mathlib.Data.Fin.Rev

namespace SpectralRadiusUpperTail
open scoped BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] {N : ℕ}

lemma sum_fin_reverse {E : Type*} [AddCommMonoid E] (f : Fin N → E) :
    (∑ i : Fin N, f i.rev) = ∑ i : Fin N, f i :=
  Equiv.sum_comp Fin.revPerm f

lemma weightedPrefix_zeroExtend (v x : Fin N → 𝕂) (j : Fin N) :
    weightedPrefix (zeroExtendVector v) (zeroExtendVector x) j.val =
      ∑ i : Fin N, if i.val < j.val then v i*x i else 0 := by
  unfold weightedPrefix
  rw [← sum_fin_prefix (fun k => zeroExtendVector v k*zeroExtendVector x k) j]
  simp only [zeroExtendVector_fin]

/-- Reversal turns the ascending revealed prefix into the actual descending mask. -/
lemma upperRowTarget_reverse (v : ℕ → 𝕂) (j : Fin N) (t : 𝕂) (x : Fin N → 𝕂) :
    upperRowTarget v j t x = t-
      weightedPrefix (zeroExtendVector (fun i : Fin N => v i.rev.val))
        (zeroExtendVector (fun i : Fin N => x i.rev)) j.rev.val := by
  rw [weightedPrefix_zeroExtend]
  unfold upperRowTarget upperRowCoefficients
  simp only [ite_mul, zero_mul]
  congr 1
  rw [← sum_fin_reverse (fun i : Fin N =>
    if i.val < j.rev.val then v i.rev.val*x i.rev else 0)]
  simp only [Fin.rev_rev, ← Fin.lt_def, Fin.rev_lt_rev]

lemma sum_fin_through (f : ℕ → ℝ) (j : Fin N) :
    (∑ i : Fin N, if i.val ≤ j.val then f i.val else 0) =
      (∑ i : Fin j.val, f i.val)+f j.val := by
  have hsplit : (∑ i : Fin N, if i.val ≤ j.val then f i.val else 0) =
      (∑ i : Fin N, if i.val < j.val then f i.val else 0)+f j.val := by
    calc
      _ = ∑ i : Fin N, ((if i.val < j.val then f i.val else 0)+
        (if i=j then f j.val else 0)) := by
          apply Finset.sum_congr rfl
          intro i _
          by_cases hij : i=j
          · subst i; simp
          · have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
            by_cases hlt : i.val < j.val
            · simp [hlt, hlt.le, hij]
            · have hnot : ¬i.val ≤ j.val := by omega
              simp [hlt, hnot, hij]
      _ = _ := by rw [Finset.sum_add_distrib]; simp
  rw [hsplit, sum_fin_prefix f j, Fin.sum_univ_eq_sum_range f j.val]

/-- The full descending regression denominator is the ascending tail denominator
of the reversed vector, including the current coordinate. -/
lemma tailDenominator_reverse (η : ℝ) (v : ℕ → 𝕂) (j : Fin N) :
    tailDenominator η (fun i : Fin N => v i.rev.val) j.rev.val =
      η+(∑ i : Fin j.val, ‖v i.val‖^2)+‖v j.val‖^2 := by
  unfold tailDenominator
  rw [← sum_fin_reverse (fun i : Fin N =>
    if j.rev.val ≤ i.val then ‖v i.rev.val‖^2 else 0)]
  simp only [Fin.rev_rev, ← Fin.le_def, Fin.rev_le_rev]
  rw [show (∑ i : Fin N, if i ≤ j then ‖v i.val‖^2 else 0) =
    (∑ i : Fin j.val, ‖v i.val‖^2)+‖v j.val‖^2 from
      sum_fin_through (fun i => ‖v i‖^2) j]
  ring

#print axioms upperRowTarget_reverse
#print axioms tailDenominator_reverse
end SpectralRadiusUpperTail
