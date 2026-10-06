import SpectralRadiusUpperTail.OccurrenceWordSerialization

namespace SpectralRadiusUpperTail

/-- A finite family of occurrence words, with lengths recorded explicitly to
keep later dependent domains independent of ambient vertices. -/
structure OccurrenceFamily (L : ℕ) where
  count : ℕ
  lengths : Fin count → ℕ
  words : ∀ i, Fin (lengths i) → Fin L × Bool

def OccurrenceFamily.rows {L : ℕ} (W : OccurrenceFamily L) := occurrenceWordRows W.words

/-- The row list determines the full dependent family, including its number
of tours and all lengths. These need not be independently counted. -/
lemma OccurrenceFamily.rows_injective {L : ℕ} :
    Function.Injective (@OccurrenceFamily.rows L) := by
  rintro ⟨t,n,w⟩ ⟨u,m,z⟩ h
  have ht := congrArg List.length h
  simp only [OccurrenceFamily.rows,occurrenceWordRows,List.length_ofFn] at ht
  subst u
  have hn := congrArg (List.map List.length) h
  simp only [OccurrenceFamily.rows,occurrenceWordRows,List.map_ofFn,Function.comp_def,
    List.length_ofFn] at hn
  have hn' : n = m := List.ofFn_inj.mp hn
  subst m
  have hw : w = z := occurrenceWordRows_injective h
  subst z
  rfl

abbrev OccurrenceFamily.VertexSlot {L : ℕ} (W : OccurrenceFamily L) :=
  Σ i : Fin W.count, Fin (W.lengths i+1)

variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
variable {s : Fin (2*r) → Bool} {v : Fin (2*r+1) → V}

noncomputable def DefectRouteCertificate.occurrenceFamily (c : DefectRouteCertificate s v) :
    OccurrenceFamily (2*r) :=
  ⟨c.indexedTours.length,fun i => (c.indexedTours.get i).tokens.length,c.indexedWord⟩

lemma DefectRouteCertificate.occurrenceFamily_rows (c : DefectRouteCertificate s v) :
    c.occurrenceFamily.rows = c.indexedTours.map SegmentRoute.tokens := c.indexedWord_rows

#print axioms OccurrenceFamily
#print axioms OccurrenceFamily.rows
#print axioms OccurrenceFamily.rows_injective
#print axioms OccurrenceFamily.VertexSlot
#print axioms DefectRouteCertificate.occurrenceFamily
#print axioms DefectRouteCertificate.occurrenceFamily_rows
end SpectralRadiusUpperTail
