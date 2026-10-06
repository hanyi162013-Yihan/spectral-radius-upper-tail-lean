import SpectralRadiusUpperTail.GaussianRevealedEntry

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂] {N : ℕ}

/-- The already revealed coordinates when the next coordinate is j. -/
def upperRowHistory (j : Fin N) (x : Fin N → 𝕂) : Fin (N-(j.val+1)) → 𝕂 :=
  fun i => x ⟨j.val+1+i.val, by omega⟩

def upperRowCoefficients (v : ℕ → 𝕂) (j : Fin N) : Fin N → 𝕂 :=
  fun i => if j.val < i.val then v i.val else 0

def upperRowTarget (v : ℕ → 𝕂) (j : Fin N) (t : 𝕂) (x : Fin N → 𝕂) : 𝕂 :=
  t-∑ i, upperRowCoefficients v j i*x i

omit [MeasurableSpace 𝕂] [BorelSpace 𝕂] [SecondCountableTopology 𝕂] in
lemma upperRowCoefficients_energy (v : ℕ → 𝕂) (j : Fin N)
    (hv : ∑ i : Fin N, ‖v i.val‖^2 ≤ 1) :
    ∑ i, ‖upperRowCoefficients v j i‖^2 ≤ 1 := by
  apply le_trans (Finset.sum_le_sum (fun i _ => ?_)) hv
  unfold upperRowCoefficients
  split_ifs
  · exact le_rfl
  · simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact sq_nonneg _

omit [MeasurableSpace 𝕂] [BorelSpace 𝕂] [SecondCountableTopology 𝕂] in
lemma current_future_energy (v : ℕ → 𝕂) (j : Fin N)
    (hv : ∑ i : Fin N, ‖v i.val‖^2 ≤ 1) :
    ‖v j.val‖^2+∑ i : Fin j.val, ‖v i.val‖^2 ≤ 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => ‖v i‖^2) N] at hv
  rw [Fin.sum_univ_eq_sum_range (fun i => ‖v i‖^2) j.val]
  rw [add_comm, ← Finset.sum_range_succ]
  apply le_trans ?_ hv
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
    (fun i _ _ => sq_nonneg _)

omit [MeasurableSpace 𝕂] [BorelSpace 𝕂] [SecondCountableTopology 𝕂] in
lemma upperRowTarget_continuous (v : ℕ → 𝕂) (j : Fin N) (t : 𝕂) :
    Continuous (upperRowTarget v j t) := by
  unfold upperRowTarget
  fun_prop

omit [MeasurableSpace 𝕂] [BorelSpace 𝕂] [SecondCountableTopology 𝕂] in
/-- The coefficient mask is exactly the stored history of the descending
sequential construction, with all index conversions made explicit. -/
lemma upperRowHistory_revealedSum (v : ℕ → 𝕂) (j : Fin N) (x : Fin N → 𝕂) :
    revealedSum (fun i z => v i*z) N (N-(j.val+1)) (upperRowHistory j x) =
      ∑ i, upperRowCoefficients v j i*x i := by
  have hj : N-(N-(j.val+1)) = j.val+1 := by omega
  unfold revealedSum upperRowHistory upperRowCoefficients
  simp only [hj, ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun (i : Fin (N-(j.val+1))) _ =>
    (⟨j.val+1+i.val, by omega⟩ : Fin N))
  · intro i _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  · intro i _ k _ hik
    apply Fin.ext
    have hh := congrArg Fin.val hik
    dsimp at hh
    omega
  · intro i hi
    have hi' : j.val < i.val := (Finset.mem_filter.mp hi).2
    refine ⟨⟨i.val-(j.val+1), by omega⟩, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    dsimp
    omega
  · intro i _
    rfl

/-- The full-row masked target selects the exact transition law of the actual
coupling, not an independently introduced regression proxy. -/
theorem upperRowEntryLaw_eq_transition (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (v : ℕ → 𝕂) (j : Fin N)
    (a : ℝ) (ha : 0 < a) (t : 𝕂) (x : Fin N → 𝕂) :
    gaussianEntryLaw μ a (fun i : Fin j.val => v i.val) (v j.val) (upperRowTarget v j t x) =
      μ.withDensity (doobDensity N
        (revealedWeight μ (fun i z => v i*z) (gaussianSoftWeight a) N t)
        (N-(j.val+1)) (upperRowHistory j x)) := by
  have hn : N-(j.val+1) < N := by omega
  have hj : N-(N-(j.val+1)+1) = j.val := by omega
  have hh := gaussianEntryLaw_eq_revealed_transition μ hX v N (N-(j.val+1)) hn a ha
    t (upperRowHistory j x)
  rw [hj, upperRowHistory_revealedSum] at hh
  exact hh

#print axioms current_future_energy
#print axioms upperRowHistory_revealedSum
#print axioms upperRowEntryLaw_eq_transition
end SpectralRadiusUpperTail
