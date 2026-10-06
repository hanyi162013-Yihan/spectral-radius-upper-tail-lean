import SpectralRadiusUpperTail.SchurPathWaitingFirstEdge

namespace SpectralRadiusUpperTail

/-- Under the first-edge reindexing, each path/waiting term factors into
the first diagonal power, the first bridge, and the shorter tail term. -/
theorem schurPathWaitingFirstEdge_term (d N k l : ℕ) (hlk : l < k)
    (D : Fin N → Matrix (Fin d) (Fin d) ℝ)
    (U : Matrix (Fin N) (Fin N) (Matrix (Fin d) (Fin d) ℝ))
    (v : Σ i : Fin N, Σ s : Fin (k-l),
      {q : IncreasingBlockPath N l // i < q.val 0} ×
        SchurWaitingTimes (k-s.val-1) l) :
    schurStrictPathTerm d N (l+1) D U
      ((schurPathWaitingFirstEdgeEquiv N k l hlk).symm v).1.val
      ((schurPathWaitingFirstEdgeEquiv N k l hlk).symm v).2.val =
      (D v.1)^(v.2.1.val) * U v.1 (v.2.2.1.val.val 0) *
        schurStrictPathTerm d N l D U v.2.2.1.val.val v.2.2.2.val := by
  rcases v with ⟨i, s, q, t⟩
  change schurStrictPathTerm d N (l+1) D U
      (Fin.cons i q.val.val) (Fin.cons s.val t.val) =
    (D i)^s.val * U i (q.val.val 0) *
      schurStrictPathTerm d N l D U q.val.val t.val
  exact schurStrictPathTerm_cons d N l D U i q.val.val s.val t.val

#print axioms schurPathWaitingFirstEdge_term
end SpectralRadiusUpperTail
