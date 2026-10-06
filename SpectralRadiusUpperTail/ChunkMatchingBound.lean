import SpectralRadiusUpperTail.ChunkIntervalCoverage
import SpectralRadiusUpperTail.FragmentCountMatchingBound
import SpectralRadiusUpperTail.ConstantRunPartition

namespace SpectralRadiusUpperTail

/-- A concrete list of constant-sign fragments directly supplies all interval
hypotheses of the sharp matching estimate. Empty fragments are harmless here. -/
lemma chunk_matching_count_le (C : List (List Bool))
    (hconst : ∀ c ∈ C, labelConstant id c)
    (m L B K : ℕ) (hmL : m ≤ L) (hlen : ∀ c ∈ C, c.length ≤ m)
    (hnum : C.length ≤ B+K) :
    Nat.card (SignedNoncrossingMatching (fun i : Fin C.flatten.length => C.flatten.get i)) ≤
      (m+1)^B * (L+1)^K := by
  have hs : ∀ b : Fin C.length, ∀ i j : Fin (C.get b).length,
      C.flatten.get (chunkInterval C b i) = C.flatten.get (chunkInterval C b j) := by
    intro b i j
    rw [chunkInterval_get,chunkInterval_get]
    exact hconst _ (List.get_mem _ b) _ (List.get_mem _ i) _ (List.get_mem _ j)
  exact fragmentCount_matching_count_le _ (fun b : Fin C.length => (C.get b).length)
    (chunkInterval C) (chunkInterval_cover C) (chunkInterval_strictMono C)
    (chunkInterval_convex C) hs m L B K hmL
    (fun b => hlen _ (List.get_mem _ b)) (by simpa only [Fintype.card_fin] using hnum)

#print axioms chunk_matching_count_le
end SpectralRadiusUpperTail
