import SpectralRadiusUpperTail.SegmentEndpointParity

namespace SpectralRadiusUpperTail
variable {α V M : Type*} [DecidableEq V] [AddCommMonoid M]

/-- Even endpoint incidences suffice to assemble valid segments into closed
segments. A commutative payload is conserved exactly, so original segment labels
can be retained with their full multiplicities. Loops and parallel edges are
allowed; the proof uses strictly fewer segments at every recursive step. -/
lemma segmentClosedAssembly (start finish : α → V) (reverse : α → α)
    (join : α → α → α) (mass : α → M) (Valid : α → Prop)
    (hrs : ∀ a, start (reverse a) = finish a)
    (hrf : ∀ a, finish (reverse a) = start a)
    (hrm : ∀ a, mass (reverse a) = mass a)
    (hrv : ∀ a, Valid a → Valid (reverse a))
    (hjs : ∀ a b, start (join a b) = start a)
    (hjf : ∀ a b, finish (join a b) = finish b)
    (hjm : ∀ a b, mass (join a b) = mass a + mass b)
    (hjv : ∀ a b, Valid a → Valid b → finish a = start b → Valid (join a b))
    (L : List α) (hvalid : ∀ a ∈ L, Valid a)
    (heven : ∀ x, Even (segmentEndpointCount start finish L x)) :
    ∃ K : List α, (∀ a ∈ K, Valid a ∧ start a = finish a) ∧
      K.length ≤ L.length ∧ (K.map mass).sum = (L.map mass).sum := by
  suffices hmain : ∀ n (L : List α), L.length = n →
      (∀ a ∈ L, Valid a) → (∀ x, Even (segmentEndpointCount start finish L x)) →
      ∃ K : List α, (∀ a ∈ K, Valid a ∧ start a = finish a) ∧
        K.length ≤ L.length ∧ (K.map mass).sum = (L.map mass).sum by
    exact hmain L.length L rfl hvalid heven
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro L hn hvalid heven
    cases L with
    | nil => exact ⟨[],by simp,by simp,by simp⟩
    | cons a tail =>
      have hva : Valid a := hvalid a (by simp)
      have hvt : ∀ b ∈ tail, Valid b := fun b hb => hvalid b (by simp [hb])
      by_cases ha : start a = finish a
      · have he := segmentEndpoint_even_remove_closed start finish a tail ha heven
        obtain ⟨K,hK,hsize,hmass⟩ := ih tail.length (by simp only [List.length_cons] at hn; omega) tail rfl hvt he
        refine ⟨a::K,?_,?_,?_⟩
        · intro b hb
          rcases List.mem_cons.mp hb with rfl | hb
          · exact ⟨hva,ha⟩
          · exact hK b hb
        · simpa using Nat.add_le_add_right hsize 1
        · simpa [hmass]
      · obtain ⟨b,hb,hincident⟩ := segmentEndpoint_exists_incident start finish a tail ha heven
        obtain ⟨pre,post,htail⟩ := List.mem_iff_append.mp hb
        let rest := pre ++ post
        have hperm : tail.Perm (b::rest) := by
          rw [htail]
          exact List.perm_middle
        have hperm' := hperm.cons a
        have he : ∀ x, Even (segmentEndpointCount start finish (a::b::rest) x) := by
          intro x
          rw [← segmentEndpointCount_perm start finish hperm' x]
          exact heven x
        have hvr : ∀ c ∈ rest, Valid c := by
          intro c hc
          apply hvt c
          exact hperm.mem_iff.mpr (List.mem_cons_of_mem b hc)
        have hvb : Valid b := hvt b hb
        have hor : ∃ b', start b' = finish a ∧ Valid b' ∧ mass b' = mass b ∧
            (∀ x, Even (segmentEndpointCount start finish (a::b'::rest) x)) := by
          rcases hincident with hab | hab
          · exact ⟨b,hab,hvb,rfl,he⟩
          · refine ⟨reverse b,(hrs b).trans hab,hrv b hvb,hrm b,?_⟩
            exact segmentEndpoint_reverse_even start finish a b (reverse b) rest
              (hrs b) (hrf b) he
        obtain ⟨b',hb's,hb'v,hb'm,hb'e⟩ := hor
        let c := join a b'
        have hvc : Valid c := hjv a b' hva hb'v hb's.symm
        have hec := segmentEndpoint_merge_even start finish a b' c rest
          hb's.symm (hjs a b') (hjf a b') hb'e
        have hlen : (c::rest).length < n := by
          have hh := hperm.length_eq
          simp only [List.length_cons] at hh hn ⊢
          omega
        have hvcr : ∀ d ∈ c::rest, Valid d := by
          intro d hd
          rcases List.mem_cons.mp hd with rfl | hd
          · exact hvc
          · exact hvr d hd
        obtain ⟨K,hK,hsize,hmass⟩ := ih (c::rest).length hlen (c::rest) rfl hvcr hec
        refine ⟨K,hK,?_,?_⟩
        · rw [hn]
          exact hsize.trans (Nat.le_of_lt hlen)
        · rw [hmass]
          have hp := (hperm'.map mass).sum_eq
          rw [hp]
          simp [c,hjm,hb'm,add_assoc]

#print axioms segmentClosedAssembly
end SpectralRadiusUpperTail
