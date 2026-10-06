import SpectralRadiusUpperTail.GaussianBridgeModel

namespace SpectralRadiusUpperTail
open scoped BigOperators

/-- Internal row/column choices for a chain containing `l` random blocks. -/
def MatrixChainIndex (d : ℕ) : ℕ → Type
  | 0 => Unit
  | l+1 => MatrixChainIndex d l × (Fin d × Fin d)

instance matrixChainIndexFintype (d : ℕ) : (l : ℕ) → Fintype (MatrixChainIndex d l)
  | 0 => inferInstanceAs (Fintype Unit)
  | l+1 => @instFintypeProd _ _ (matrixChainIndexFintype d l) inferInstance

noncomputable def gaussianMatrixChain (d : ℕ) : (l : ℕ) →
    (Fin (l+1) → Matrix (Fin d) (Fin d) ℝ) →
    (Fin l → Matrix (Fin d) (Fin d) ℝ) → Matrix (Fin d) (Fin d) ℝ
  | 0, D, _ => D 0
  | l+1, D, G => gaussianMatrixChain d l (fun i => D i.castSucc) (fun i => G i.castSucc) *
      G (Fin.last l) * D (Fin.last (l+1))

noncomputable def matrixChainCoefficient (d : ℕ) : (l : ℕ) →
    (Fin (l+1) → Matrix (Fin d) (Fin d) ℝ) → Fin d → Fin d → MatrixChainIndex d l → ℝ
  | 0, D, a, b, _ => D 0 a b
  | l+1, D, a, b, u =>
      matrixChainCoefficient d l (fun i => D i.castSucc) a u.2.1 u.1 *
      D (Fin.last (l+1)) u.2.2 b

/-- The scalar coordinate selected from each of the random blocks. -/
def matrixChainWord {σ : Type*} (d : ℕ) : (l : ℕ) →
    (Fin l → Fin d → Fin d → σ) → MatrixChainIndex d l → Fin l → σ
  | 0, _, _ => Fin.elim0
  | l+1, e, u => Fin.snoc
      (matrixChainWord d l (fun j => e j.castSucc) u.1)
      (e (Fin.last l) u.2.1 u.2.2)

/-- Full scalar expansion; no independence or distributional assumptions. -/
theorem matrixChain_expansion {σ : Type*} (d l : ℕ)
    (D : Fin (l+1) → Matrix (Fin d) (Fin d) ℝ)
    (e : Fin l → Fin d → Fin d → σ) (x : σ → ℝ) (a b : Fin d) :
    gaussianMatrixChain d l D (fun j => Matrix.of (fun r s => x (e j r s))) a b =
      ∑ u : MatrixChainIndex d l,
        matrixChainCoefficient d l D a b u * ∏ j, x (matrixChainWord d l e u j) := by
  induction l generalizing a b with
  | zero =>
    change D 0 a b = ∑ u : Unit, matrixChainCoefficient d 0 D a b u * ∏ j : Fin 0, _
    simp [matrixChainCoefficient]
  | succ l ih =>
    simp only [gaussianMatrixChain, Matrix.mul_apply, Matrix.of_apply]
    simp_rw [ih]
    change _ = ∑ u : MatrixChainIndex d l × (Fin d × Fin d), _
    simp only [Fintype.sum_prod_type, matrixChainCoefficient, matrixChainWord]
    simp_rw [Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
    simp_rw [Finset.sum_mul]
    let H := fun (s r : Fin d) (u : MatrixChainIndex d l) =>
      (matrixChainCoefficient d l (fun i => D i.castSucc) a r u *
        ∏ j, x (matrixChainWord d l (fun j => e j.castSucc) u j)) *
        x (e (Fin.last l) r s) * D (Fin.last (l+1)) s b
    change (∑ s, ∑ r, ∑ u, H s r u) = _
    calc
      _ = ∑ s, ∑ u, ∑ r, H s r u := by
        apply Finset.sum_congr rfl
        intro s _
        exact Finset.sum_comm
      _ = ∑ u, ∑ s, ∑ r, H s r u := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro u _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro r _
        apply Finset.sum_congr rfl
        intro s _
        dsimp [H]
        ring

lemma matrixChainWord_project {σ τ : Type*} (d l : ℕ) (π : σ → τ)
    (e : Fin l → Fin d → Fin d → σ) (p : Fin l → τ)
    (he : ∀ j r s, π (e j r s) = p j) (u : MatrixChainIndex d l) :
    (fun j => π (matrixChainWord d l e u j)) = p := by
  induction l with
  | zero => exact funext (fun j => Fin.elim0 j)
  | succ l ih =>
    apply funext
    intro j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa only [matrixChainWord, Fin.snoc_last] using he (Fin.last l) u.2.1 u.2.2
    · simpa only [matrixChainWord, Fin.snoc_castSucc] using
        congrFun (ih (fun j => e j.castSucc) (fun j => p j.castSucc)
          (fun j r s => he j.castSucc r s) u.1) j

#print axioms matrixChain_expansion
#print axioms matrixChainWord_project
end SpectralRadiusUpperTail
