import SpectralRadiusUpperTail.RealSchurMixedChartSpectrum

namespace SpectralRadiusUpperTail
open scoped Matrix

theorem blockDiagonal_left_compress_mul
    {ι β : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq β]
    (b : ι → β) (A B : Matrix ι ι ℝ)
    (hA : ∀ i j, b i ≠ b j → A i j = 0) (a : β) :
    (A*B).toSquareBlock b a = A.toSquareBlock b a * B.toSquareBlock b a := by
  classical
  let p := fun i => b i=a
  change (A*B).toBlock p p = A.toBlock p p * B.toBlock p p
  rw [Matrix.toBlock_mul_eq_add p p p]
  have hz : A.toBlock p (fun i => ¬p i) = 0 := by
    ext i j
    exact hA i.val j.val (fun h => j.property (h.symm.trans i.property))
  rw [hz, Matrix.zero_mul, add_zero]

theorem blockDiagonal_right_compress_mul
    {ι β : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq β]
    (b : ι → β) (A B : Matrix ι ι ℝ)
    (hB : ∀ i j, b i ≠ b j → B i j = 0) (a : β) :
    (A*B).toSquareBlock b a = A.toSquareBlock b a * B.toSquareBlock b a := by
  classical
  let p := fun i => b i=a
  change (A*B).toBlock p p = A.toBlock p p * B.toBlock p p
  rw [Matrix.toBlock_mul_eq_add p p p]
  have hz : B.toBlock (fun i => ¬p i) p = 0 := by
    ext i j
    exact hB i.val j.val (fun h => i.property (h.trans j.property))
  rw [hz, Matrix.mul_zero, add_zero]

theorem blockDiagonal_orthogonal_compression
    {ι β : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq β]
    (b : ι → β) (W : Matrix ι ι ℝ) (hW : Wᵀ*W=1)
    (hoff : ∀ i j, b i ≠ b j → W i j = 0) (a : β) :
    (W.toSquareBlock b a)ᵀ * W.toSquareBlock b a = 1 := by
  have ht : ∀ i j, b i ≠ b j → Wᵀ i j = 0 :=
    fun i j hij => hoff j i hij.symm
  have he := congrArg (fun A : Matrix ι ι ℝ => A.toSquareBlock b a) hW
  rw [blockDiagonal_left_compress_mul b Wᵀ W ht a] at he
  change (W.toSquareBlock b a)ᵀ * W.toSquareBlock b a =
    (1 : Matrix ι ι ℝ).toBlock (fun i => b i=a) (fun i => b i=a) at he
  rwa [Matrix.toBlock_one_self] at he

/-- Conjugation within the diagonal blocks preserves the ordered Schur
form and every diagonal-block characteristic polynomial. -/
theorem blockDiagonal_orthogonal_conjugation
    {ι β : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder β]
    (b : ι → β) (W T : Matrix ι ι ℝ) (hW : Wᵀ*W=1)
    (hoff : ∀ i j, b i ≠ b j → W i j = 0)
    (hT : T.BlockTriangular b) :
    (W*T*Wᵀ).BlockTriangular b ∧
      ∀ a, ((W*T*Wᵀ).toSquareBlock b a).charpoly = (T.toSquareBlock b a).charpoly := by
  have ht : ∀ i j, b i ≠ b j → Wᵀ i j = 0 :=
    fun i j hij => hoff j i hij.symm
  have hup : W.BlockTriangular b := fun i j hij => hoff i j (ne_of_gt hij)
  have hupt : Wᵀ.BlockTriangular b := fun i j hij => ht i j (ne_of_gt hij)
  refine ⟨(hup.mul hT).mul hupt,?_⟩
  intro a
  rw [blockDiagonal_right_compress_mul b (W*T) Wᵀ ht a,
    blockDiagonal_left_compress_mul b W T hoff a]
  change (W.toSquareBlock b a*T.toSquareBlock b a*(W.toSquareBlock b a)ᵀ).charpoly = _
  exact realMatrixOrthogonalConjugation_charpoly _ _ _
    (blockDiagonal_orthogonal_compression b W hW hoff a)

#print axioms blockDiagonal_left_compress_mul
#print axioms blockDiagonal_right_compress_mul
#print axioms blockDiagonal_orthogonal_compression
#print axioms blockDiagonal_orthogonal_conjugation
end SpectralRadiusUpperTail
