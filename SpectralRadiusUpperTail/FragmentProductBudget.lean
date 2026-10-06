import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card

namespace SpectralRadiusUpperTail
open scoped BigOperators

/-- Splitting one original sign block retains its leading m+1 factor and
costs at most one L+1 factor for each additional fragment. -/
lemma fragment_product_le (l : List ℕ) (m L : ℕ) (hmL : m ≤ L)
    (hm : ∀ a ∈ l, a ≤ m) :
    (l.map (fun a => a+1)).prod ≤ (m+1)*(L+1)^(l.length-1) := by
  cases l with
  | nil => simp
  | cons a l =>
    have htail : (l.map (fun a => a+1)).prod ≤ (L+1)^l.length := by
      have h := List.prod_le_pow_card (l := l.map (fun a => a+1)) (L+1) (by
        intro x hx
        obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hx
        exact Nat.add_le_add_right ((hm b (List.mem_cons_of_mem a hb)).trans hmL) 1)
      simpa only [List.length_map] using h
    simpa only [List.map_cons,List.prod_cons,List.length_cons,Nat.add_sub_cancel] using
      Nat.mul_le_mul (Nat.add_le_add_right (hm a (by simp)) 1) htail

/-- Conditional algebraic cost for a family of original sign blocks. The
actual fragment construction must separately prove the extra-fragment budget. -/
lemma fragment_family_product_le {B : Type*} [Fintype B]
    (l : B → List ℕ) (m L K : ℕ) (hmL : m ≤ L)
    (hm : ∀ b a, a ∈ l b → a ≤ m)
    (hcuts : (∑ b, ((l b).length-1)) ≤ K) :
    (∏ b, ((l b).map (fun a => a+1)).prod) ≤
      (m+1)^Fintype.card B * (L+1)^K := by
  classical
  calc
    _ ≤ ∏ b, ((m+1)*(L+1)^((l b).length-1)) :=
      Finset.prod_le_prod' (fun b _ => fragment_product_le (l b) m L hmL (hm b))
    _ = (m+1)^Fintype.card B * (L+1)^(∑ b, ((l b).length-1)) := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const,Finset.card_univ,← Finset.prod_pow_eq_pow_sum]
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hcuts)

#print axioms fragment_product_le
#print axioms fragment_family_product_le
end SpectralRadiusUpperTail
