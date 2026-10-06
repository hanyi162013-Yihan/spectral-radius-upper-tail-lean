import SpectralRadiusUpperTail.SequentialIndependence
import Mathlib.MeasureTheory.Constructions.Pi

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
variable {α Θ β : Type*} [MeasurableSpace α] [MeasurableSpace Θ] [MeasurableSpace β]

lemma measurable_fin_cons (n : ℕ) :
    Measurable (fun z : (Fin n → α) × α => (Fin.cons z.2 z.1 : Fin (n+1) → α)) := by
  apply measurable_pi_lambda
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [Fin.cons_zero] using
      (measurable_snd : Measurable (fun z : (Fin n → α) × α => z.2))
  · simpa only [Fin.cons_succ, Function.comp_def] using
      (measurable_pi_apply j).comp measurable_fst

def comparatorVector (n : ℕ) (z : Fin n → α × α) : Fin n → α := fun i => (z i).2

lemma measurable_comparatorVector (n : ℕ) : Measurable (comparatorVector (α := α) n) :=
  measurable_pi_lambda _ (fun i => measurable_snd.comp (measurable_pi_apply i))

lemma compProd_comparator_project (P : Measure Θ) [SFinite P]
    (κ : Kernel Θ (α × α)) [IsSFiniteKernel κ] (μ : Measure α) [SFinite μ]
    (hκ : ∀ s, (κ s).map Prod.snd = μ) (f : Θ → β) (hf : Measurable f) :
    (P ⊗ₘ κ).map (fun z : Θ × (α × α) => (f z.1,z.2.2)) = (P.map f).prod μ := by
  have hT : Measurable (fun z : Θ × (α × α) => (z.1,z.2.2)) :=
    measurable_fst.prodMk (measurable_snd.comp measurable_snd)
  calc
    _ = ((P ⊗ₘ κ).map (fun z : Θ × (α × α) => (z.1,z.2.2))).map (Prod.map f id) := by
      rw [Measure.map_map (hf.prodMap measurable_id) hT]
      rfl
    _ = (P.prod μ).map (Prod.map f id) := by rw [compProd_comparator_joint P κ μ hκ]
    _ = (P.map f).prod μ := by
      rw [← Measure.map_prod_map P μ hf measurable_id, Measure.map_id]

lemma iid_cons_map (μ : Measure α) [IsProbabilityMeasure μ] (n : ℕ) :
    ((Measure.pi (fun _ : Fin n => μ)).prod μ).map
        (fun z : (Fin n → α) × α => Fin.cons z.2 z.1) =
      Measure.pi (fun _ : Fin (n+1) => μ) := by
  have hdir : Measurable (fun z : α × (Fin n → α) => (Fin.cons z.1 z.2 : Fin (n+1) → α)) :=
    (measurable_fin_cons n).comp measurable_swap
  calc
    _ = (((Measure.pi (fun _ : Fin n => μ)).prod μ).map Prod.swap).map
        (fun z : α × (Fin n → α) => Fin.cons z.1 z.2) := by
      rw [Measure.map_map hdir measurable_swap]
      rfl
    _ = (μ.prod (Measure.pi (fun _ : Fin n => μ))).map
        (fun z : α × (Fin n → α) => Fin.cons z.1 z.2) := by rw [Measure.prod_swap]
    _ = _ := by
      simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_zero,
        Fin.consEquiv, Equiv.coe_fn_mk] using
        (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) 0).symm.map_eq

lemma comparator_cons_step (μ : Measure α) [IsProbabilityMeasure μ] (n : ℕ)
    (P : Measure (Fin n → α × α)) [IsProbabilityMeasure P]
    (κ : Kernel (Fin n → α × α) (α × α)) [IsMarkovKernel κ]
    (hκ : ∀ s, (κ s).map Prod.snd = μ)
    (hP : P.map (comparatorVector n) = Measure.pi (fun _ : Fin n => μ)) :
    ((P ⊗ₘ κ).map (fun z : (Fin n → α × α) × (α × α) => Fin.cons z.2 z.1)).map
        (comparatorVector (n+1)) = Measure.pi (fun _ : Fin (n+1) => μ) := by
  have hQ : Measurable (fun z : (Fin n → α × α) × (α × α) =>
      (comparatorVector n z.1,z.2.2)) :=
    ((measurable_comparatorVector n).comp measurable_fst).prodMk
      (measurable_snd.comp measurable_snd)
  have hfun : comparatorVector (n+1) ∘
      (fun z : (Fin n → α × α) × (α × α) => Fin.cons z.2 z.1) =
      (fun z : (Fin n → α) × α => Fin.cons z.2 z.1) ∘
        (fun z : (Fin n → α × α) × (α × α) => (comparatorVector n z.1,z.2.2)) := by
    funext z i
    exact Fin.cases rfl (fun _ => rfl) i
  rw [Measure.map_map (measurable_comparatorVector (n+1)) (measurable_fin_cons n), hfun,
    ← Measure.map_map (measurable_fin_cons n) hQ,
    compProd_comparator_project P κ μ hκ (comparatorVector n) (measurable_comparatorVector n),
    hP, iid_cons_map]

/-- A concrete finite sequential coupled array. The newest pair is stored first. -/
noncomputable def finiteCoupledLaw
    (κ : (n : ℕ) → Kernel (Fin n → α × α) (α × α)) :
    (n : ℕ) → Measure (Fin n → α × α)
  | 0 => Measure.dirac (fun i => Fin.elim0 i)
  | n+1 => ((finiteCoupledLaw κ n) ⊗ₘ (κ n)).map
      (fun z : (Fin n → α × α) × (α × α) => Fin.cons z.2 z.1)

instance finiteCoupledLaw_probability
    (κ : (n : ℕ) → Kernel (Fin n → α × α) (α × α)) [∀ n, IsMarkovKernel (κ n)]
    (n : ℕ) : IsProbabilityMeasure (finiteCoupledLaw κ n) := by
  induction n with
  | zero => unfold finiteCoupledLaw; infer_instance
  | succ n ih =>
    let : IsProbabilityMeasure (finiteCoupledLaw κ n) := ih
    rw [finiteCoupledLaw]
    exact Measure.isProbabilityMeasure_map (measurable_fin_cons n).aemeasurable

/-- The entire comparator array has the exact iid product law, for every
finite length, even though the first coordinates may depend on all the past. -/
theorem finiteCoupledLaw_comparator_iid (μ : Measure α) [IsProbabilityMeasure μ]
    (κ : (n : ℕ) → Kernel (Fin n → α × α) (α × α)) [∀ n, IsMarkovKernel (κ n)]
    (hκ : ∀ n s, (κ n s).map Prod.snd = μ) (n : ℕ) :
    (finiteCoupledLaw κ n).map (comparatorVector n) = Measure.pi (fun _ : Fin n => μ) := by
  induction n with
  | zero =>
    rw [finiteCoupledLaw, Measure.map_dirac' (measurable_comparatorVector 0),
      Measure.pi_of_empty]
    congr 1
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    exact comparator_cons_step μ n (finiteCoupledLaw κ n) (κ n) (hκ n) ih

#print axioms finiteCoupledLaw_comparator_iid
end SpectralRadiusUpperTail
