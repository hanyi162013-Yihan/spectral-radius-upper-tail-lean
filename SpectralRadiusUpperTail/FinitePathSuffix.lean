import SpectralRadiusUpperTail.FiniteSequentialLaw

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
variable {α : Type*} [MeasurableSpace α]

/-- The first n revealed coordinates of a terminal path, stored as its suffix. -/
def pathSuffix (m n : ℕ) (h : n ≤ m) (x : Fin m → α) : Fin n → α :=
  fun i => x ⟨m-n+i.val, by omega⟩

lemma pathSuffix_measurable (m n : ℕ) (h : n ≤ m) :
    Measurable (pathSuffix (α := α) m n h) :=
  measurable_pi_lambda _ (fun _ => measurable_pi_apply _)

lemma pathSuffix_self (m : ℕ) : pathSuffix (α := α) m m le_rfl = id := by
  funext x i
  unfold pathSuffix
  congr 1
  apply Fin.ext
  simp

lemma pathSuffix_comp (m n k : ℕ) (hn : n ≤ m) (hk : k ≤ n) :
    pathSuffix (α := α) n k hk ∘ pathSuffix m n hn = pathSuffix m k (hk.trans hn) := by
  funext x i
  simp only [pathSuffix, Function.comp_def]
  congr 1
  apply Fin.ext
  dsimp
  omega

lemma pathSuffix_cons (m n : ℕ) (h : n ≤ m) (x : Fin m → α) (y : α) :
    pathSuffix (m+1) n (by omega) (Fin.cons y x) = pathSuffix m n h x := by
  funext i
  unfold pathSuffix
  have hi : (⟨m+1-n+i.val, by omega⟩ : Fin (m+1)) =
      (⟨m-n+i.val, by omega⟩ : Fin m).succ := by apply Fin.ext; dsimp; omega
  rw [hi, Fin.cons_succ]

/-- The terminal law remembers the exact law of every earlier paired history. -/
theorem finiteCoupledLaw_suffix
    (κ : (n : ℕ) → Kernel (Fin n → α × α) (α × α)) [∀ n, IsMarkovKernel (κ n)]
    (m n : ℕ) (h : n ≤ m) :
    (finiteCoupledLaw κ m).map (pathSuffix m n h) = finiteCoupledLaw κ n := by
  induction m with
  | zero =>
    have hn : n=0 := by omega
    subst n
    rw [pathSuffix_self, Measure.map_id]
  | succ m ih =>
    by_cases hn : n ≤ m
    · rw [finiteCoupledLaw, Measure.map_map (pathSuffix_measurable _ _ _) (measurable_fin_cons m)]
      have he : pathSuffix (m+1) n h ∘
          (fun z : (Fin m → α × α) × (α × α) => Fin.cons z.2 z.1) =
          pathSuffix m n hn ∘ Prod.fst := by
        funext z
        exact pathSuffix_cons m n hn z.1 z.2
      rw [he, ← Measure.map_map (pathSuffix_measurable _ _ _) measurable_fst]
      change ((finiteCoupledLaw κ m ⊗ₘ κ m).fst).map (pathSuffix m n hn) = _
      rw [Measure.fst_compProd, ih hn]
    · have he : n=m+1 := by omega
      subst n
      rw [pathSuffix_self, Measure.map_id]

#print axioms finiteCoupledLaw_suffix
end SpectralRadiusUpperTail
