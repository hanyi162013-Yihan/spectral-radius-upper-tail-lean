import SpectralRadiusUpperTail.WalkFamilyGluingPairs
import SpectralRadiusUpperTail.AmbientMatchingReconstruction

namespace SpectralRadiusUpperTail
variable {I V W : Type*} [Fintype I] [Fintype V] [Fintype W]
variable [DecidableEq V] [DecidableEq W] {n : I → ℕ}

/-- The local relation on primitive slots is determined solely by each tour's
own vertex equality pattern, even when ambient vertex types differ. -/
lemma walkFamilyLocalMap_eq_iff_of_local_patterns
    (p : ∀ i, Fin (n i+1) → V) (q : ∀ i, Fin (n i+1) → W)
    (h : ∀ i a b, p i a = p i b ↔ q i a = q i b)
    (x y : Σ i, Fin (n i+1)) :
    walkFamilyLocalMap p x = walkFamilyLocalMap p y ↔
      walkFamilyLocalMap q x = walkFamilyLocalMap q y := by
  classical
  obtain ⟨i,a⟩ := x
  obtain ⟨j,b⟩ := y
  by_cases hij : i = j
  · subst j
    simp only [walkFamilyLocalMap, Sigma.mk.inj_iff, heq_iff_eq, true_and]
    constructor
    · intro he
      exact Subtype.ext ((h i a b).mp (congrArg Subtype.val he))
    · intro he
      exact Subtype.ext ((h i a b).mpr (congrArg Subtype.val he))
  · constructor
    · intro he
      exact (hij (congrArg Sigma.fst he)).elim
    · intro he
      exact (hij (congrArg Sigma.fst he)).elim

/-- Once local patterns and gluing pairs agree, the surviving global vertex
pattern is identical. The reconstruction is by equivalence closure. -/
lemma walkFamily_global_pattern_of_gluing
    (p : ∀ i, Fin (n i+1) → V) (q : ∀ i, Fin (n i+1) → W)
    (hlocal : ∀ i a b, p i a = p i b ↔ q i a = q i b)
    (E : Finset ((Σ i, Fin (n i+1)) × (Σ i, Fin (n i+1))))
    (hp : ∀ x y, Relation.EqvGen
      (fun a b => walkFamilyLocalMap p a = walkFamilyLocalMap p b ∨ (a,b) ∈ E) x y ↔
        p x.1 x.2 = p y.1 y.2)
    (hq : ∀ x y, Relation.EqvGen
      (fun a b => walkFamilyLocalMap q a = walkFamilyLocalMap q b ∨ (a,b) ∈ E) x y ↔
        q x.1 x.2 = q y.1 y.2)
    (x y : Σ i, Fin (n i+1)) : p x.1 x.2 = p y.1 y.2 ↔ q x.1 x.2 = q y.1 y.2 := by
  have he : (fun a b => walkFamilyLocalMap p a = walkFamilyLocalMap p b ∨ (a,b) ∈ E) =
      (fun a b => walkFamilyLocalMap q a = walkFamilyLocalMap q b ∨ (a,b) ∈ E) := by
    funext a b
    exact propext (or_congr (walkFamilyLocalMap_eq_iff_of_local_patterns p q hlocal a b) Iff.rfl)
  rw [← hp, ← hq, he]

#print axioms walkFamilyLocalMap_eq_iff_of_local_patterns
#print axioms walkFamily_global_pattern_of_gluing
end SpectralRadiusUpperTail
