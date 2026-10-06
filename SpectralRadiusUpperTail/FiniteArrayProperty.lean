import SpectralRadiusUpperTail.FiniteArrayMartingale

namespace SpectralRadiusUpperTail
variable {Ω E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {M N : ℕ}

/-- Transport a time-dependent property of coordinate increments to
every serialized time, including zero continuation after the array. -/
lemma finiteArrayIncrement_property (d : Fin M → Fin N → Ω → E)
    (P : ℕ → (Ω → E) → Prop) (hd : ∀ i j, P (i.val*N+j.val) (d i j))
    (hz : ∀ r, P r 0) (r : ℕ) : P r (finiteArrayIncrement d r) := by
  by_cases hr : r < M*N
  · rw [finiteArrayIncrement, dif_pos hr]
    have hh := hd (finProdFinEquiv.symm (⟨r,hr⟩ : Fin (M*N))).1
      (finProdFinEquiv.symm (⟨r,hr⟩ : Fin (M*N))).2
    rwa [finiteArray_index_time] at hh
  · rw [finiteArrayIncrement, dif_neg hr]
    exact hz r

#print axioms finiteArrayIncrement_property
end SpectralRadiusUpperTail
