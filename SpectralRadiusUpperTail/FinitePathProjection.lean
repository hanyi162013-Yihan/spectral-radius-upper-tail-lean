import SpectralRadiusUpperTail.KernelProjection
import SpectralRadiusUpperTail.FiniteSequentialLaw

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

def coordinateVector (g : α → β) (n : ℕ) (x : Fin n → α) : Fin n → β :=
  fun i => g (x i)

lemma measurable_coordinateVector (g : α → β) (hg : Measurable g) (n : ℕ) :
    Measurable (coordinateVector g n) :=
  measurable_pi_lambda _ (fun i => hg.comp (measurable_pi_apply i))

noncomputable def finitePathLaw (κ : (n : ℕ) → Kernel (Fin n → α) α) :
    (n : ℕ) → Measure (Fin n → α)
  | 0 => Measure.dirac (fun i => Fin.elim0 i)
  | n+1 => ((finitePathLaw κ n) ⊗ₘ (κ n)).map
      (fun z : (Fin n → α) × α => Fin.cons z.2 z.1)

instance finitePathLaw_probability
    (κ : (n : ℕ) → Kernel (Fin n → α) α) [∀ n, IsMarkovKernel (κ n)]
    (n : ℕ) : IsProbabilityMeasure (finitePathLaw κ n) := by
  induction n with
  | zero => unfold finitePathLaw; infer_instance
  | succ n ih =>
    let : IsProbabilityMeasure (finitePathLaw κ n) := ih
    rw [finitePathLaw]
    exact Measure.isProbabilityMeasure_map (measurable_fin_cons n).aemeasurable

/-- Exact finite-dimensional preservation of transition laws under a
coordinate projection, proved for the recursively constructed measures. -/
theorem finitePathLaw_projection
    (κ : (n : ℕ) → Kernel (Fin n → α) α) [∀ n, IsMarkovKernel (κ n)]
    (η : (n : ℕ) → Kernel (Fin n → β) β) [∀ n, IsMarkovKernel (η n)]
    (g : α → β) (hg : Measurable g)
    (hκ : ∀ n s, (κ n s).map g = η n (coordinateVector g n s)) (n : ℕ) :
    (finitePathLaw κ n).map (coordinateVector g n) = finitePathLaw η n := by
  induction n with
  | zero =>
    rw [finitePathLaw, Measure.map_dirac' (measurable_coordinateVector g hg 0), finitePathLaw]
    congr 1
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    have hfun : coordinateVector g (n+1) ∘
        (fun z : (Fin n → α) × α => Fin.cons z.2 z.1) =
        (fun z : (Fin n → β) × β => Fin.cons z.2 z.1) ∘
          Prod.map (coordinateVector g n) g := by
      funext z i
      exact Fin.cases rfl (fun _ => rfl) i
    change (((finitePathLaw κ n) ⊗ₘ (κ n)).map
      (fun z : (Fin n → α) × α => Fin.cons z.2 z.1)).map (coordinateVector g (n+1)) =
        (((finitePathLaw η n) ⊗ₘ (η n)).map
          (fun z : (Fin n → β) × β => Fin.cons z.2 z.1))
    rw [Measure.map_map (measurable_coordinateVector g hg (n+1)) (measurable_fin_cons n),
      hfun, ← Measure.map_map (measurable_fin_cons n)
        ((measurable_coordinateVector g hg n).prodMap hg),
      compProd_projection (finitePathLaw κ n) (κ n) (η n) (coordinateVector g n) g
        (measurable_coordinateVector g hg n) hg (hκ n), ih]

lemma finiteCoupledLaw_eq_pathLaw
    (κ : (n : ℕ) → Kernel (Fin n → α × α) (α × α)) (n : ℕ) :
    finiteCoupledLaw κ n = finitePathLaw κ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [finiteCoupledLaw, finitePathLaw, ih]

theorem finiteCoupledLaw_source_law
    (κ : (n : ℕ) → Kernel (Fin n → α × α) (α × α)) [∀ n, IsMarkovKernel (κ n)]
    (η : (n : ℕ) → Kernel (Fin n → α) α) [∀ n, IsMarkovKernel (η n)]
    (hκ : ∀ n s, (κ n s).map Prod.fst = η n (coordinateVector Prod.fst n s)) (n : ℕ) :
    (finiteCoupledLaw κ n).map (coordinateVector Prod.fst n) = finitePathLaw η n := by
  rw [finiteCoupledLaw_eq_pathLaw]
  exact finitePathLaw_projection κ η Prod.fst measurable_fst hκ n

#print axioms finitePathLaw_projection
#print axioms finiteCoupledLaw_source_law
end SpectralRadiusUpperTail
