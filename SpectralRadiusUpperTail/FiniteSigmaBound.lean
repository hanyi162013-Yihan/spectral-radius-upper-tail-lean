import Mathlib.Data.Fintype.BigOperators
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace SpectralRadiusUpperTail
open scoped BigOperators

lemma finite_sigma_count_le {I : Type*} [Finite I] (F : I → Type*) [∀ i, Finite (F i)]
    (M : ℕ) (hM : ∀ i, Nat.card (F i) ≤ M) :
    Nat.card (Σ i, F i) ≤ Nat.card I * M := by
  classical
  letI : Fintype I := Fintype.ofFinite I
  letI (i : I) : Fintype (F i) := Fintype.ofFinite (F i)
  simp only [Nat.card_eq_fintype_card,Fintype.card_sigma] at hM ⊢
  calc
    (∑ i, Fintype.card (F i)) ≤ ∑ _i : I, M := Finset.sum_le_sum (fun i _ => hM i)
    _ = Fintype.card I * M := by simp

lemma subsingleton_sigma_count_le {I : Type*} [Subsingleton I]
    (F : I → Type*) [∀ i, Finite (F i)] (M : ℕ) (hM : ∀ i, Nat.card (F i) ≤ M) :
    Nat.card (Σ i, F i) ≤ M := by
  have h := finite_sigma_count_le F M hM
  letI : Fintype I := Fintype.ofFinite I
  have hi : Nat.card I ≤ 1 := by
    simpa only [Nat.card_eq_fintype_card,Finset.card_univ] using
      (Finset.card_le_one_of_subsingleton (Finset.univ : Finset I))
  exact h.trans ((Nat.mul_le_mul_right M hi).trans (by simp))

#print axioms finite_sigma_count_le
#print axioms subsingleton_sigma_count_le
end SpectralRadiusUpperTail
