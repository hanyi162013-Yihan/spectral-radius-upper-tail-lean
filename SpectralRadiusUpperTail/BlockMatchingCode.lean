import SpectralRadiusUpperTail.NoncrossingOpeningUnique
import SpectralRadiusUpperTail.InitialSegmentCard

namespace SpectralRadiusUpperTail

abbrev NoncrossingMatching (n : ℕ) :=
  {f : Fin n → Fin n // Function.Involutive f ∧ (∀ i, f i ≠ i) ∧
    ∀ a b, a < b → b < f a → f a < f b → False}

abbrev BlockClosingMatching {n m : ℕ} {β : Type*} (v : β → Fin m → Fin n) :=
  {f : NoncrossingMatching n // ∀ b, IsLowerSet {i : Fin m | f.val (v b i) < v b i}}

noncomputable def blockMatchingCode {n m : ℕ} {β : Type*}
    (v : β → Fin m → Fin n) (f : BlockClosingMatching v) : β → Fin (m+1) := by
  classical
  exact fun b => initialSegmentCode
    ⟨Finset.univ.filter (fun i => f.val.val (v b i) < v b i), by simpa using f.property b⟩

lemma blockMatchingCode_injective {n m : ℕ} {β : Type*}
    (v : β → Fin m → Fin n) (hcover : ∀ i, ∃ b j, v b j = i) :
    Function.Injective (blockMatchingCode v) := by
  classical
  intro f g h
  apply Subtype.ext
  apply Subtype.ext
  apply noncrossing_matching_eq_of_openings f.val.val g.val.val
    f.val.property.1 g.val.property.1 f.val.property.2.1 g.val.property.2.1
    f.val.property.2.2 g.val.property.2.2
  intro i
  obtain ⟨b,j,hj⟩ := hcover i
  have he := congrFun h b
  have hs := initialSegmentCode_injective m he
  have ht := congrArg Subtype.val hs
  have hm : (f.val.val (v b j) < v b j) ↔ (g.val.val (v b j) < v b j) := by
    have hh := Finset.ext_iff.mp ht j
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hh
  rw [hj] at hm
  have hnf := f.val.property.2.1 i
  have hng := g.val.property.2.1 i
  omega

#print axioms NoncrossingMatching
#print axioms BlockClosingMatching
#print axioms blockMatchingCode
#print axioms blockMatchingCode_injective
end SpectralRadiusUpperTail
