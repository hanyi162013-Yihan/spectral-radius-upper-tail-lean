import SpectralRadiusUpperTail.IidMixedMoments
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {σ τ υ 𝕂 : Type*} [Fintype σ] [DecidableEq σ] [Fintype τ] [Fintype υ]

/-- Number of occurrences of a matrix-entry index in a finite word. -/
def entryMultiplicity (e : τ → σ) (i : σ) : ℕ :=
  (Finset.univ.filter (fun j => e j = i)).card

lemma entryWord_product_eq_powers [CommMonoid 𝕂] (e : τ → σ) (x : σ → 𝕂) :
    (∏ j, x (e j)) = ∏ i, (x i)^(entryMultiplicity e i) := by
  simpa only [entryMultiplicity, Finset.prod_const] using
    (Finset.prod_fiberwise' Finset.univ e x).symm

lemma entryWord_pair_eq_mixed [CommSemiring 𝕂] [StarRing 𝕂]
    (e : τ → σ) (f : υ → σ) (x : σ → 𝕂) :
    (∏ j, x (e j))*(∏ j, star (x (f j))) =
      ∏ i, (x i)^(entryMultiplicity e i)*(star (x i))^(entryMultiplicity f i) := by
  rw [entryWord_product_eq_powers e x, entryWord_product_eq_powers f (fun i => star (x i)),
    Finset.prod_mul_distrib]

/-- A directed edge occurring exactly once across a pair of words makes the
actual iid paired-word expectation zero. -/
lemma iidWordPair_singleton_zero [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
    (μ : Measure 𝕂) [IsProbabilityMeasure μ] (hm : (∫ x : 𝕂, x ∂μ) = 0)
    (e : τ → σ) (f : υ → σ) (i : σ)
    (hi : entryMultiplicity e i+entryMultiplicity f i = 1) :
    (∫ x : σ → 𝕂, (∏ j, x (e j))*(∏ j, star (x (f j)))
      ∂Measure.pi (fun _ : σ => μ)) = 0 := by
  simp_rw [entryWord_pair_eq_mixed]
  exact iidMixedProduct_singleton_zero μ hm _ _ i hi

#print axioms entryWord_product_eq_powers
#print axioms entryWord_pair_eq_mixed
#print axioms iidWordPair_singleton_zero
end SpectralRadiusUpperTail
