import SpectralRadiusUpperTail.OccurrenceKernelCode

namespace SpectralRadiusUpperTail

abbrev OccurrenceFamily.Matchings {L : ℕ} (W : OccurrenceFamily L) :=
  ∀ i : Fin W.count, SignedNoncrossingMatching (fun j => (W.words i j).2)

noncomputable def OccurrenceFamily.matchingCard {L : ℕ} (W : OccurrenceFamily L) : ℕ :=
  Nat.card W.Matchings

#print axioms OccurrenceFamily.Matchings
#print axioms OccurrenceFamily.matchingCard
end SpectralRadiusUpperTail
