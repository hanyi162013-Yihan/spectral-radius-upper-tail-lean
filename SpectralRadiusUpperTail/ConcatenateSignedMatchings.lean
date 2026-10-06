import SpectralRadiusUpperTail.AppendSignedMatching

namespace SpectralRadiusUpperTail

abbrev FiniteSignWord := Σ n : ℕ, Fin n → Bool

def signWordLength (W : List FiniteSignWord) : ℕ := (W.map Sigma.fst).sum

def concatenateSigns : (W : List FiniteSignWord) → Fin (signWordLength W) → Bool
  | [] => Fin.elim0
  | w :: W => Fin.addCases w.2 (concatenateSigns W)

def SignedMatchingFamily : List FiniteSignWord → Type
  | [] => PUnit
  | w :: W => SignedNoncrossingMatching w.2 × SignedMatchingFamily W

def concatenateSignedMatchings : (W : List FiniteSignWord) →
    SignedMatchingFamily W → SignedNoncrossingMatching (concatenateSigns W)
  | [], _ => ⟨⟨Fin.elim0, (fun i => Fin.elim0 i),
      (fun i => Fin.elim0 i), (fun i => Fin.elim0 i)⟩,fun i => Fin.elim0 i⟩
  | w :: W, f => appendSignedMatching f.1 (concatenateSignedMatchings W f.2)

/-- Every component matching can be recovered from the concatenation. -/
lemma concatenateSignedMatchings_injective (W : List FiniteSignWord) :
    Function.Injective (concatenateSignedMatchings W) := by
  induction W with
  | nil =>
    intro f g _
    exact @Subsingleton.elim PUnit inferInstance f g
  | cons w W ih =>
    intro f g h
    have hp : (f.1, concatenateSignedMatchings W f.2) =
        (g.1, concatenateSignedMatchings W g.2) := appendSignedMatching_injective h
    have hleft := congrArg
      (@Prod.fst (SignedNoncrossingMatching w.2)
        (SignedNoncrossingMatching (concatenateSigns W))) hp
    have hright := congrArg
      (@Prod.snd (SignedNoncrossingMatching w.2)
        (SignedNoncrossingMatching (concatenateSigns W))) hp
    exact Prod.ext hleft (ih hright)

instance signedMatchingFamily_finite (W : List FiniteSignWord) : Finite (SignedMatchingFamily W) := by
  induction W with
  | nil => dsimp [SignedMatchingFamily]; infer_instance
  | cons w W ih => dsimp [SignedMatchingFamily]; infer_instance

lemma signedMatchingFamily_card (W : List FiniteSignWord) :
    Nat.card (SignedMatchingFamily W) = (W.map (fun w => Nat.card (SignedNoncrossingMatching w.2))).prod := by
  induction W with
  | nil => simp [SignedMatchingFamily]
  | cons w W ih => simpa only [SignedMatchingFamily,Nat.card_prod,List.map_cons,List.prod_cons,ih]

/-- Local matching counts are bounded by the count for the concatenated sign
word; this introduces no extra factor for the number of tours. -/
lemma concatenateSignedMatchings_count_le (W : List FiniteSignWord) :
    (W.map (fun w => Nat.card (SignedNoncrossingMatching w.2))).prod ≤
      Nat.card (SignedNoncrossingMatching (concatenateSigns W)) := by
  classical
  letI : Fintype (SignedMatchingFamily W) := Fintype.ofFinite _
  letI : Fintype (SignedNoncrossingMatching (concatenateSigns W)) := Fintype.ofFinite _
  rw [← signedMatchingFamily_card]
  simpa only [Nat.card_eq_fintype_card] using
    Fintype.card_le_of_injective _ (concatenateSignedMatchings_injective W)

#print axioms FiniteSignWord
#print axioms signWordLength
#print axioms concatenateSigns
#print axioms SignedMatchingFamily
#print axioms concatenateSignedMatchings
#print axioms concatenateSignedMatchings_injective
#print axioms signedMatchingFamily_finite
#print axioms signedMatchingFamily_card
#print axioms concatenateSignedMatchings_count_le
end SpectralRadiusUpperTail
