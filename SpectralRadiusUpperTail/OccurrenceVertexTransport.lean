import SpectralRadiusUpperTail.SignedWalkSupport
import SpectralRadiusUpperTail.RetainedPositionExtension

namespace SpectralRadiusUpperTail
variable {I V : Type*} {L : ℕ} {n : I → ℕ}

/-- Select the endpoint representing the initial vertex of an original step.
The expanded sign can differ from the original sign after segment reversal. -/
def occurrenceInitialSlot (s : Fin L → Bool) (words : ∀ i, Fin (n i) → Fin L × Bool)
    (i : I) (j : Fin (n i)) : Fin (n i+1) :=
  if s (words i j).1 = (words i j).2 then j.castSucc else j.succ

lemma occurrenceInitialSlot_vertex (s : Fin L → Bool) (v : Fin (L+1) → V)
    (words : ∀ i, Fin (n i) → Fin L × Bool) (p : ∀ i, Fin (n i+1) → V)
    (he : ∀ i j, orientedWalkEdge (fun a => (words i a).2) (p i) j =
      orientedWalkEdge s v (words i j).1) (i : I) (j : Fin (n i)) :
    p i (occurrenceInitialSlot s words i j) = v (words i j).1.castSucc := by
  have h := he i j
  cases hs : s (words i j).1 <;> cases ht : (words i j).2 <;>
    simp only [orientedWalkEdge,hs,ht,Bool.false_eq_true,if_false,if_true] at h <;>
    simp only [occurrenceInitialSlot,hs,ht,Bool.false_eq_true,Bool.true_eq_false,if_false,if_true] <;>
    first | exact congrArg Prod.fst h | exact congrArg Prod.snd h

/-- Pull a relation on local vertex slots back using actual occurrence labels.
No arbitrary transport function or ambient vertex labels enter this decoder. -/
def occurrencePullbackRelation (s : Fin L → Bool)
    (words : ∀ i, Fin (n i) → Fin L × Bool)
    (R : (Σ i, Fin (n i+1)) → (Σ i, Fin (n i+1)) → Prop)
    (a b : Fin (L+1)) : Prop :=
  ∃ i j k l, (words i j).1.castSucc = a ∧ (words k l).1.castSucc = b ∧
    R ⟨i,occurrenceInitialSlot s words i j⟩ ⟨k,occurrenceInitialSlot s words k l⟩

lemma occurrencePullbackRelation_iff (s : Fin L → Bool) (v : Fin (L+1) → V)
    (D : Finset (Fin L)) (words : ∀ i, Fin (n i) → Fin L × Bool)
    (p : ∀ i, Fin (n i+1) → V)
    (he : ∀ i j, orientedWalkEdge (fun a => (words i a).2) (p i) j =
      orientedWalkEdge s v (words i j).1)
    (hwords : ∀ k, (∃ i j, (words i j).1 = k) ↔ k ∉ D)
    (R : (Σ i, Fin (n i+1)) → (Σ i, Fin (n i+1)) → Prop)
    (hR : ∀ x y, R x y ↔ p x.1 x.2 = p y.1 y.2)
    (a b : Fin (L+1)) : occurrencePullbackRelation s words R a b ↔
      a ∈ retainedInitialPositions D ∧ b ∈ retainedInitialPositions D ∧ v a = v b := by
  classical
  constructor
  · rintro ⟨i,j,k,l,rfl,rfl,h⟩
    refine ⟨Finset.mem_image.mpr ⟨_,Finset.mem_compl.mpr ((hwords _).mp ⟨i,j,rfl⟩),rfl⟩,
      Finset.mem_image.mpr ⟨_,Finset.mem_compl.mpr ((hwords _).mp ⟨k,l,rfl⟩),rfl⟩,?_⟩
    have hh := (hR _ _).mp h
    simpa only [occurrenceInitialSlot_vertex s v words p he] using hh
  · rintro ⟨ha,hb,hab⟩
    obtain ⟨ka,hka,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨kb,hkb,rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨i,j,hij⟩ := (hwords ka).mpr (Finset.mem_compl.mp hka)
    obtain ⟨k,l,hkl⟩ := (hwords kb).mpr (Finset.mem_compl.mp hkb)
    refine ⟨i,j,k,l,congrArg Fin.castSucc hij,congrArg Fin.castSucc hkl,(hR _ _).mpr ?_⟩
    simp only [occurrenceInitialSlot_vertex s v words p he,hij,hkl]
    exact hab

#print axioms occurrenceInitialSlot
#print axioms occurrenceInitialSlot_vertex
#print axioms occurrencePullbackRelation
#print axioms occurrencePullbackRelation_iff
end SpectralRadiusUpperTail
