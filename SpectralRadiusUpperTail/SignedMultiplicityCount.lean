import SpectralRadiusUpperTail.IidWordCount

namespace SpectralRadiusUpperTail
open scoped BigOperators
variable {σ τ : Type*} [Fintype σ] [DecidableEq σ] [Fintype τ]

lemma entryMultiplicity_indicator_sum (e : τ → σ) (i : σ) :
    entryMultiplicity e i = ∑ t : τ, if e t = i then 1 else 0 := by
  simp only [entryMultiplicity, Finset.card_eq_sum_ones, Finset.sum_filter]

lemma signedMultiplicity_add (e : τ → σ) (s : τ → Bool) (i : σ) :
    entryMultiplicity (fun t => (e t,s t)) (i,false) +
      entryMultiplicity (fun t => (e t,s t)) (i,true) = entryMultiplicity e i := by
  simp only [entryMultiplicity_indicator_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  by_cases he : e t = i <;> cases hs : s t <;> simp [he,hs]

#print axioms entryMultiplicity_indicator_sum
#print axioms signedMultiplicity_add
end SpectralRadiusUpperTail
