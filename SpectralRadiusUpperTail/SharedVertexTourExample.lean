import SpectralRadiusUpperTail.SegmentRoute
import SpectralRadiusUpperTail.SignedBlockMatchingCount

namespace SpectralRadiusUpperTail

/-- A two-step return route; its middle vertex need not be private to the route. -/
def twoStepReturnRoute {V : Type*} (a b : V) : SegmentRoute V (V × V) :=
  ⟨a,a,[((a,b),false),((a,b),true)]⟩

lemma twoStepReturnRoute_valid {V : Type*} (a b : V) :
    (twoStepReturnRoute a b).Valid (fun e => e) := by
  refine ⟨?_,by simp [twoStepReturnRoute]⟩
  exact .cons ((a,b),false) (.cons ((a,b),true) (.nil a))

/-- Positions in two separate return tours, including their repeated endpoints. -/
def twoTourVertexSlots (a b c d : Fin 3) (i : Fin 6) : Fin 3 :=
  if i.val < 3 then (if i.val = 1 then b else a)
  else (if i.val = 4 then d else c)

def twoTourEntrySlots (a b c d : Fin 3) (i : Fin 4) : Fin 3 × Fin 3 :=
  if i.val < 2 then (a,b) else (c,d)

def twoTourExampleSigns (i : Fin 4) : Bool := decide (i.val % 2 = 1)

def twoTourExamplePartner (i : Fin 4) : Fin 4 :=
  ⟨if i.val % 2 = 0 then i.val+1 else i.val-1,by
    have hi := i.isLt
    split_ifs <;> omega⟩

/-- The same signed matching pairs the two steps separately in each tour. -/
def twoTourExampleMatching : SignedNoncrossingMatching twoTourExampleSigns :=
  ⟨⟨twoTourExamplePartner,by
      change ∀ i : Fin 4, twoTourExamplePartner (twoTourExamplePartner i) = i
      decide,by decide,by decide⟩,by decide⟩

lemma twoTourExampleMatching_preserves_entries (a b c d : Fin 3) :
    ∀ i, twoTourEntrySlots a b c d (twoTourExampleMatching.val.val i) =
      twoTourEntrySlots a b c d i := by
  intro i
  fin_cases i <;> rfl

/-- Both collections have valid closed return routes and the same signs/pairing,
but their cross-tour vertex equality differs: compare a-b-a, c-b-c with
 a-b-a, a-c-a. Thus local pairings alone do not reconstruct global vertices. -/
lemma sharedVertexTourExample :
    (twoStepReturnRoute (0 : Fin 3) 1).Valid (fun e => e) ∧
    (twoStepReturnRoute (2 : Fin 3) 1).Valid (fun e => e) ∧
    (twoStepReturnRoute (0 : Fin 3) 2).Valid (fun e => e) ∧
    (∀ i, twoTourEntrySlots 0 1 2 1 (twoTourExampleMatching.val.val i) =
      twoTourEntrySlots 0 1 2 1 i) ∧
    (∀ i, twoTourEntrySlots 0 1 0 2 (twoTourExampleMatching.val.val i) =
      twoTourEntrySlots 0 1 0 2 i) ∧
    twoTourVertexSlots 0 1 2 1 1 = twoTourVertexSlots 0 1 2 1 4 ∧
    twoTourVertexSlots 0 1 2 1 0 ≠ twoTourVertexSlots 0 1 2 1 3 ∧
    twoTourVertexSlots 0 1 0 2 0 = twoTourVertexSlots 0 1 0 2 3 := by
  exact ⟨twoStepReturnRoute_valid _ _,twoStepReturnRoute_valid _ _,
    twoStepReturnRoute_valid _ _,twoTourExampleMatching_preserves_entries _ _ _ _,
    twoTourExampleMatching_preserves_entries _ _ _ _,by decide,by decide,by decide⟩

#print axioms twoStepReturnRoute
#print axioms twoStepReturnRoute_valid
#print axioms twoTourVertexSlots
#print axioms twoTourEntrySlots
#print axioms twoTourExampleSigns
#print axioms twoTourExamplePartner
#print axioms twoTourExampleMatching
#print axioms twoTourExampleMatching_preserves_entries
#print axioms sharedVertexTourExample
end SpectralRadiusUpperTail
