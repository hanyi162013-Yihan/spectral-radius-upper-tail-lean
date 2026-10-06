import SpectralRadiusUpperTail.BridgePathNoninterleaving

namespace SpectralRadiusUpperTail
variable {V : Type*}

def finPathExtend {n : ℕ} (p : Fin (n+1) → V) (t : ℕ) : V :=
  p ⟨min t n, Nat.lt_succ_of_le (Nat.min_le_right t n)⟩

lemma finPathExtend_at {n : ℕ} (p : Fin (n+1) → V) (t : Fin (n+1)) :
    finPathExtend p t.val = p t := by
  unfold finPathExtend
  apply congrArg p
  apply Fin.ext
  exact Nat.min_eq_left (Nat.le_of_lt_succ t.isLt)

lemma finiteBridgePath_no_interleaving {n : ℕ} (G : SimpleGraph V) (a b : V)
    (hb : G.IsBridge s(a,b)) (p : Fin (n+1) → V) (i k j l : Fin n)
    (hik : i < k) (hkj : k < j) (hjl : j < l)
    (hadj : ∀ t : Fin n, G.Adj (p t.castSucc) (p t.succ))
    (hj : s(p j.castSucc,p j.succ) = s(a,b))
    (hother : ∀ t : Fin n, i < t → t ≤ l → t ≠ j →
      s(p t.castSucc,p t.succ) ≠ s(a,b))
    (hpair : s(p k.castSucc,p k.succ) = s(p l.castSucc,p l.succ)) : False := by
  have hp (t : Fin n) : finPathExtend p t.val = p t.castSucc := finPathExtend_at p t.castSucc
  have hps (t : Fin n) : finPathExtend p (t.val+1) = p t.succ := finPathExtend_at p t.succ
  apply bridgePath_no_interleaving G a b hb (finPathExtend p) i.val k.val j.val l.val hik hkj hjl
  · intro t ht
    let u : Fin n := ⟨t, by omega⟩
    change G.Adj (finPathExtend p u.val) (finPathExtend p (u.val+1))
    rw [hp u, hps u]
    exact hadj u
  · simpa only [hp j,hps j] using hj
  · intro t hit htl htj
    let u : Fin n := ⟨t, by omega⟩
    change s(finPathExtend p u.val,finPathExtend p (u.val+1)) ≠ s(a,b)
    rw [hp u,hps u]
    apply hother u hit htl
    intro he
    exact htj (congrArg Fin.val he)
  · simpa only [hp k,hps k,hp l,hps l] using hpair

#print axioms finPathExtend
#print axioms finPathExtend_at
#print axioms finiteBridgePath_no_interleaving
end SpectralRadiusUpperTail
