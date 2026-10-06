import SpectralRadiusUpperTail.RealSchurMixedSimpleRegular
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped BigOperators

/-- All ordered block shapes of a fixed dimension, encoded by a finite
type. Every block has size one or two; the empty shape is allowed at zero. -/
abbrev RealSchurFiniteShape (n : ℕ) :=
  {r : Σ m : Fin (n+1), (Fin m.val → Fin 3) //
    (∀ i, (r.2 i).val=1 ∨ (r.2 i).val=2) ∧ (∑ i, (r.2 i).val)=n}

noncomputable instance (n : ℕ) : Fintype (RealSchurFiniteShape n) := by
  classical
  unfold RealSchurFiniteShape
  infer_instance

def RealSchurFiniteShape.blockCount {n : ℕ} (S : RealSchurFiniteShape n) : ℕ := S.val.1.val

def RealSchurFiniteShape.sizes {n : ℕ} (S : RealSchurFiniteShape n) :
    Fin S.blockCount → ℕ := fun i => (S.val.2 i).val

theorem RealSchurFiniteShape.sizes_small {n : ℕ} (S : RealSchurFiniteShape n) :
    ∀ i, S.sizes i=1 ∨ S.sizes i=2 := S.property.1

theorem RealSchurFiniteShape.sizes_pos {n : ℕ} (S : RealSchurFiniteShape n) :
    ∀ i, 0 < S.sizes i := by
  intro i
  rcases S.sizes_small i with h | h <;> omega

theorem RealSchurFiniteShape.sum_sizes {n : ℕ} (S : RealSchurFiniteShape n) :
    (∑ i, S.sizes i)=n := S.property.2

noncomputable def RealSchurFiniteShape.indexEquiv {n : ℕ} (S : RealSchurFiniteShape n) :
    Fin n ≃ RealSchurMixedCoord S.sizes :=
  Fintype.equivOfCardEq (by simpa only [Fintype.card_fin,Fintype.card_sigma] using S.sum_sizes.symm)

/-- Any ordinary positive one/two block shape with total size `n` is
represented in the finite shape type. -/
def RealSchurFiniteShape.ofSizes {n m : ℕ} (s : Fin m → ℕ)
    (hs : ∀ i, s i=1 ∨ s i=2) (htotal : (∑ i, s i)=n) : RealSchurFiniteShape n := by
  have hm : m ≤ n := by
    calc
      m = ∑ _ : Fin m, 1 := by simp
      _ ≤ ∑ i : Fin m, s i := by
        apply Finset.sum_le_sum
        intro i _
        rcases hs i with h | h <;> omega
      _ = n := htotal
  let r : Σ j : Fin (n+1), (Fin j.val → Fin 3) :=
    ⟨⟨m,by omega⟩,fun i => ⟨s i,by rcases hs i with h | h <;> omega⟩⟩
  exact ⟨r,hs,htotal⟩

theorem RealSchurFiniteShape.ofSizes_blockCount {n m : ℕ} (s : Fin m → ℕ)
    (hs : ∀ i, s i=1 ∨ s i=2) (htotal : (∑ i, s i)=n) :
    (RealSchurFiniteShape.ofSizes s hs htotal).blockCount=m := rfl

theorem RealSchurFiniteShape.ofSizes_sizes {n m : ℕ} (s : Fin m → ℕ)
    (hs : ∀ i, s i=1 ∨ s i=2) (htotal : (∑ i, s i)=n) :
    (RealSchurFiniteShape.ofSizes s hs htotal).sizes=s := rfl

#print axioms RealSchurFiniteShape.indexEquiv
#print axioms RealSchurFiniteShape.ofSizes
#print axioms RealSchurFiniteShape.ofSizes_sizes
end SpectralRadiusUpperTail
