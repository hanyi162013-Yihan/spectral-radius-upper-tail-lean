import SpectralRadiusUpperTail.IncreasingPathGaussianSum
import SpectralRadiusUpperTail.SchurPathFixedStart

namespace SpectralRadiusUpperTail

/-- Increasing paths of at most `k` strict edges with a prescribed start. -/
abbrev SchurFixedStartFiniteFamily (N k : ℕ) (i : Fin N) :=
  Σ l : Fin (k+1), {p : IncreasingBlockPath N l.val // p.val 0 = i}

def schurFixedStartFinitePath {N k : ℕ} {i : Fin N}
    (p : SchurFixedStartFiniteFamily N k i) : AnyIncreasingPath N :=
  ⟨p.1.val,p.2.val⟩

lemma schurFixedStartFinitePath_injective {N k : ℕ} {i : Fin N} :
    Function.Injective
      (schurFixedStartFinitePath : SchurFixedStartFiniteFamily N k i →
        AnyIncreasingPath N) := by
  intro p q h
  cases p with
  | mk l p =>
    cases q with
    | mk m q =>
      have hl : l = m := Fin.ext (congrArg Sigma.fst h)
      subst m
      have hp : p.val = q.val := by
        simpa only [schurFixedStartFinitePath, Sigma.mk.inj_iff,
          heq_iff_eq, true_and] using h
      have hpq : p = q := Subtype.ext hp
      subst q
      rfl

lemma schurFixedStartFinitePath_length_le {N k : ℕ} {i : Fin N}
    (p : SchurFixedStartFiniteFamily N k i) :
    (schurFixedStartFinitePath p).1 ≤ k :=
  Nat.lt_succ_iff.mp p.1.isLt

lemma schurFixedStartPath_card_le {N l : ℕ} (i : Fin N) :
    Fintype.card {p : IncreasingBlockPath N l // p.val 0 = i} ≤
      N.choose (l+1) := by
  calc
    _ ≤ Fintype.card (IncreasingBlockPath N l) :=
      Fintype.card_subtype_le _
    _ = N.choose (l+1) := by
      rw [← Nat.card_eq_fintype_card]
      exact increasingBlockPath_card N l

#print axioms schurFixedStartFinitePath_injective
#print axioms schurFixedStartPath_card_le
end SpectralRadiusUpperTail
