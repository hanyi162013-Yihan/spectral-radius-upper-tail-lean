import SpectralRadiusUpperTail.IndexedOccurrenceCoverage

namespace SpectralRadiusUpperTail
variable {L t : ℕ} {n : Fin t → ℕ}

def occurrenceWordRows (words : ∀ i, Fin (n i) → Fin L × Bool) :
    List (List (Fin L × Bool)) := List.ofFn (fun i => List.ofFn (words i))

lemma occurrenceWordRows_injective :
    Function.Injective (@occurrenceWordRows L t n) := by
  intro a b h
  have hrows := List.ofFn_inj.mp h
  funext i
  exact List.ofFn_inj.mp (congrFun hrows i)

variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
variable {s : Fin (2*r) → Bool} {v : Fin (2*r+1) → V}

lemma DefectRouteCertificate.indexedWord_rows (c : DefectRouteCertificate s v) :
    occurrenceWordRows c.indexedWord = c.indexedTours.map SegmentRoute.tokens := by
  have hrow (i : Fin c.indexedTours.length) :
      List.ofFn (c.indexedWord i) = (c.indexedTours.get i).tokens :=
    List.ofFn_get _
  simp only [occurrenceWordRows,hrow]
  have h := congrArg (List.map SegmentRoute.tokens) (List.ofFn_get c.indexedTours)
  simpa only [List.map_ofFn,Function.comp_def] using h

#print axioms occurrenceWordRows
#print axioms occurrenceWordRows_injective
#print axioms DefectRouteCertificate.indexedWord_rows
end SpectralRadiusUpperTail
