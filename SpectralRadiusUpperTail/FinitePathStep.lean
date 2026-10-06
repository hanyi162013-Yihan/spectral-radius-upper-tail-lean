import SpectralRadiusUpperTail.FinitePathSuffix

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
variable {α : Type*} [MeasurableSpace α]

/-- The earlier paired history and the next revealed pair, as functions of a
single terminal path. -/
def pathStep (m n : ℕ) (h : n < m) (x : Fin m → α) : (Fin n → α) × α :=
  (pathSuffix m n h.le x, x ⟨m-(n+1), by omega⟩)

lemma pathStep_measurable (m n : ℕ) (h : n < m) :
    Measurable (pathStep (α := α) m n h) :=
  (pathSuffix_measurable m n h.le).prodMk (measurable_pi_apply _)

def pathUncons (n : ℕ) (x : Fin (n+1) → α) : (Fin n → α) × α := (Fin.tail x,x 0)

lemma pathUncons_measurable (n : ℕ) : Measurable (pathUncons (α := α) n) :=
  (measurable_pi_lambda _ (fun i => measurable_pi_apply i.succ)).prodMk (measurable_pi_apply 0)

lemma pathUncons_cons (n : ℕ) :
    pathUncons n ∘ (fun z : (Fin n → α) × α => Fin.cons z.2 z.1) = id := by
  funext z
  exact Prod.ext (by funext i; simp [pathUncons, Function.comp_def, Fin.tail])
    (by simp [pathUncons, Function.comp_def])

lemma pathStep_eq_uncons_suffix (m n : ℕ) (h : n < m) :
    pathStep (α := α) m n h = pathUncons n ∘ pathSuffix m (n+1) (by omega) := by
  funext x
  apply Prod.ext
  · funext i
    change x ⟨m-n+i.val, _⟩ = x ⟨m-(n+1)+i.succ.val, _⟩
    congr 1
    apply Fin.ext
    dsimp
    omega
  · change x ⟨m-(n+1), _⟩ = x ⟨m-(n+1)+0, _⟩
    rfl

/-- The terminal history/next-pair projection is exactly the actual joint law,
which carries more information than its two separate marginals. -/
theorem finiteCoupledLaw_step
    (κ : (n : ℕ) → Kernel (Fin n → α × α) (α × α)) [∀ n, IsMarkovKernel (κ n)]
    (m n : ℕ) (h : n < m) :
    (finiteCoupledLaw κ m).map (pathStep m n h) = (finiteCoupledLaw κ n) ⊗ₘ κ n := by
  rw [pathStep_eq_uncons_suffix,
    ← Measure.map_map (pathUncons_measurable n) (pathSuffix_measurable _ _ _),
    finiteCoupledLaw_suffix, finiteCoupledLaw,
    Measure.map_map (pathUncons_measurable n) (measurable_fin_cons n),
    pathUncons_cons, Measure.map_id]

#print axioms finiteCoupledLaw_step
end SpectralRadiusUpperTail
