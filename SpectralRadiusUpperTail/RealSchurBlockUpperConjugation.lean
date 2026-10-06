import SpectralRadiusUpperTail.RealSchurStrictUpperConjugation

namespace SpectralRadiusUpperTail
open scoped Matrix

def realSchurMixedDiagonalConjugation {m : ℕ} (s : Fin m → ℕ)
    (W : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (d : RealSchurMixedDiagonalEntry s → ℝ) : RealSchurMixedDiagonalEntry s → ℝ :=
  fun p => (W*realSchurMixedUpperEntryJoin s d 0*Wᵀ) p.1.1 p.1.2

theorem realSchurMixedDiagonalConjugation_embed
    {m : ℕ} (s : Fin m → ℕ)
    (W : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hoff : ∀ i j : RealSchurMixedCoord s, i.1 ≠ j.1 → W i j=0)
    (d : RealSchurMixedDiagonalEntry s → ℝ) :
    realSchurMixedUpperEntryJoin s (realSchurMixedDiagonalConjugation s W d) 0 =
      W*realSchurMixedUpperEntryJoin s d 0*Wᵀ := by
  have hs := blockDiagonal_mul_support
    (fun i : RealSchurMixedCoord s => i.1) Eq W (realSchurMixedUpperEntryJoin s d 0) hoff
    (fun i j hij => by simp [realSchurMixedUpperEntryJoin,hij])
  ext i j
  by_cases hij : i.1=j.1
  · simp [realSchurMixedUpperEntryJoin,hij,realSchurMixedDiagonalConjugation]
  · simp [realSchurMixedUpperEntryJoin,hij,hs i j hij]

theorem realSchurMixedUpperEntryJoin_eq_add
    {m : ℕ} (s : Fin m → ℕ) (d : RealSchurMixedDiagonalEntry s → ℝ)
    (u : RealSchurMixedStrictUpperEntry s → ℝ) :
    realSchurMixedUpperEntryJoin s d u =
      realSchurMixedUpperEntryJoin s d 0+realSchurMixedUpperEntryJoin s 0 u := by
  ext i j
  simp only [realSchurMixedUpperEntryJoin,Matrix.add_apply]
  split_ifs <;> simp

/-- A blockwise rotation acts separately on the diagonal entries and
strict-upper entries; the latter action is the energy-preserving map. -/
theorem realSchurMixedUpperEntryJoin_conjugation
    {m : ℕ} (s : Fin m → ℕ)
    (W : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hoff : ∀ i j : RealSchurMixedCoord s, i.1 ≠ j.1 → W i j=0)
    (d : RealSchurMixedDiagonalEntry s → ℝ) (u : RealSchurMixedStrictUpperEntry s → ℝ) :
    realSchurMixedUpperEntryJoin s (realSchurMixedDiagonalConjugation s W d)
      (realSchurMixedStrictUpperConjugationLinear s W u) =
      W*realSchurMixedUpperEntryJoin s d u*Wᵀ := by
  conv_lhs => rw [realSchurMixedUpperEntryJoin_eq_add]
  rw [realSchurMixedDiagonalConjugation_embed s W hoff d,
    realSchurMixedStrictUpperConjugation_embed s W hoff u]
  conv_rhs => rw [realSchurMixedUpperEntryJoin_eq_add]
  rw [Matrix.mul_add,Matrix.add_mul]

#print axioms realSchurMixedDiagonalConjugation_embed
#print axioms realSchurMixedUpperEntryJoin_eq_add
#print axioms realSchurMixedUpperEntryJoin_conjugation
end SpectralRadiusUpperTail
