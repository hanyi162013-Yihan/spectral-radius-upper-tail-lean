import SpectralRadiusUpperTail.BridgePathNoninterleaving

namespace SpectralRadiusUpperTail
variable {V : Type*}

lemma bridgeCutColor_same_iff_other_edge (G : SimpleGraph V) (a b u v : V)
    (hb : G.IsBridge s(a,b)) (huv : G.Adj u v) :
    bridgeCutColor G a b u = bridgeCutColor G a b v ↔ s(u,v) ≠ s(a,b) := by
  constructor
  · intro hc he
    exact bridgeCutColor_ne_of_edge_eq G a b u v hb he hc
  · exact bridgeCutColor_same_of_other_edge G a b u v huv

#print axioms bridgeCutColor_same_iff_other_edge
end SpectralRadiusUpperTail
