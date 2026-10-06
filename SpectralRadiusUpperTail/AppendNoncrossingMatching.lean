import SpectralRadiusUpperTail.SignedBlockMatchingCount
import Mathlib.Data.Fin.Basic

namespace SpectralRadiusUpperTail
variable {n m : ℕ}

/-- Place two matchings on consecutive, disjoint intervals. -/
def appendMatchingFn (f : Fin n → Fin n) (g : Fin m → Fin m) : Fin (n+m) → Fin (n+m) :=
  Fin.addCases (fun i => (f i).castAdd m) (fun i => Fin.natAdd n (g i))

@[simp] lemma appendMatchingFn_left (f : Fin n → Fin n) (g : Fin m → Fin m) (i : Fin n) :
    appendMatchingFn f g (i.castAdd m) = (f i).castAdd m := by
  simp [appendMatchingFn]

@[simp] lemma appendMatchingFn_right (f : Fin n → Fin n) (g : Fin m → Fin m) (i : Fin m) :
    appendMatchingFn f g (Fin.natAdd n i) = Fin.natAdd n (g i) := by
  simp [appendMatchingFn]

lemma appendMatchingFn_involutive (f : Fin n → Fin n) (g : Fin m → Fin m)
    (hf : Function.Involutive f) (hg : Function.Involutive g) :
    Function.Involutive (appendMatchingFn f g) := by
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [hf j]
  · simp [hg j]

lemma appendMatchingFn_no_fixed (f : Fin n → Fin n) (g : Fin m → Fin m)
    (hf : ∀ i, f i ≠ i) (hg : ∀ i, g i ≠ i) :
    ∀ i, appendMatchingFn f g i ≠ i := by
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa using hf j
  · simpa using hg j

lemma appendMatchingFn_noncrossing (f : NoncrossingMatching n) (g : NoncrossingMatching m) :
    ∀ a b, a < b → b < appendMatchingFn f.val g.val a →
      appendMatchingFn f.val g.val a < appendMatchingFn f.val g.val b → False := by
  intro a b
  refine Fin.addCases (fun i => ?_) (fun i => ?_) a
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) b
    · simpa only [appendMatchingFn_left,Fin.lt_def,Fin.val_castAdd] using f.property.2.2 i j
    · simp only [appendMatchingFn_left,appendMatchingFn_right,Fin.lt_def,Fin.val_castAdd,Fin.val_natAdd]
      have hi := (f.val i).isLt
      omega
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) b
    · simp only [appendMatchingFn_left,appendMatchingFn_right,Fin.lt_def,Fin.val_castAdd,Fin.val_natAdd]
      have hj := j.isLt
      omega
    · simpa only [appendMatchingFn_right,Fin.natAdd_lt_natAdd_iff] using g.property.2.2 i j

def appendNoncrossingMatching (f : NoncrossingMatching n) (g : NoncrossingMatching m) :
    NoncrossingMatching (n+m) :=
  ⟨appendMatchingFn f.val g.val,
    appendMatchingFn_involutive f.val g.val f.property.1 g.property.1,
    appendMatchingFn_no_fixed f.val g.val f.property.2.1 g.property.2.1,
    appendMatchingFn_noncrossing f g⟩

#print axioms appendMatchingFn
#print axioms appendMatchingFn_left
#print axioms appendMatchingFn_right
#print axioms appendMatchingFn_involutive
#print axioms appendMatchingFn_no_fixed
#print axioms appendMatchingFn_noncrossing
#print axioms appendNoncrossingMatching
end SpectralRadiusUpperTail
