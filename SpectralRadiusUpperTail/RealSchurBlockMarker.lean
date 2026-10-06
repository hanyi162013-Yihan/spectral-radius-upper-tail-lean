import SpectralRadiusUpperTail.RealSchurDiagonalSpectralOverlap

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- A symmetric marker for an ordered orthogonal block flag. It depends
only on the frame and prescribed block labels, not on Schur entries. -/
noncomputable def realSchurBlockMarker
    {ι β : Type*} [Fintype ι] [DecidableEq ι]
    (b : ι → β) (c : β → ℝ) (Q : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  Q * Matrix.diagonal (fun i => c (b i)) * Qᵀ

theorem blockDiagonal_commute_blockScalar
    {ι β : Type*} [Fintype ι] [DecidableEq ι]
    (b : ι → β) (c : β → ℝ) (W : Matrix ι ι ℝ)
    (hW : ∀ i j, b i ≠ b j → W i j = 0) :
    W * Matrix.diagonal (fun i => c (b i)) =
      Matrix.diagonal (fun i => c (b i)) * W := by
  ext i j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hij : b i = b j
  · simp [hij, mul_comm]
  · simp [hW i j hij]

/-- Orthogonal changes inside blocks leave the flag marker unchanged. -/
theorem realSchurBlockMarker_eq_of_offBlock
    {ι β : Type*} [Fintype ι] [DecidableEq ι]
    (b : ι → β) (c : β → ℝ) (Q R : Matrix ι ι ℝ)
    (hQ : Qᵀ*Q=1) (hR : Rᵀ*R=1)
    (hW : ∀ i j, b i ≠ b j → (Qᵀ*R) i j = 0) :
    realSchurBlockMarker b c Q = realSchurBlockMarker b c R := by
  have hQQ : Q*Qᵀ=1 := mul_eq_one_comm.mp hQ
  have hRR : R*Rᵀ=1 := mul_eq_one_comm.mp hR
  have hc := blockDiagonal_commute_blockScalar b c (Qᵀ*R) hW
  let D := Matrix.diagonal (fun i => c (b i))
  change Q*D*Qᵀ = R*D*Rᵀ
  calc
    Q*D*Qᵀ = Q*(D*(Qᵀ*R))*Rᵀ := by
      simp only [Matrix.mul_assoc, hRR, Matrix.mul_one]
    _ = Q*((Qᵀ*R)*D)*Rᵀ := by rw [← hc]
    _ = R*D*Rᵀ := by
      simp only [← Matrix.mul_assoc, hQQ, Matrix.one_mul]

/-- Equal markers with distinct block labels force a block-diagonal
relative frame, so the marker records exactly the ordered block flag. -/
theorem realSchurBlockMarker_offBlock_of_eq
    {ι β : Type*} [Fintype ι] [DecidableEq ι]
    (b : ι → β) (c : β → ℝ) (hc : Function.Injective c)
    (Q R : Matrix ι ι ℝ) (hQ : Qᵀ*Q=1) (hR : Rᵀ*R=1)
    (hmarker : realSchurBlockMarker b c Q = realSchurBlockMarker b c R)
    (i j : ι) (hij : b i ≠ b j) : (Qᵀ*R) i j = 0 := by
  let D := Matrix.diagonal (fun i => c (b i))
  have hcomm : D*(Qᵀ*R) = (Qᵀ*R)*D := by
    calc
      D*(Qᵀ*R) = Qᵀ*(Q*D*Qᵀ)*R := by
        simp only [← Matrix.mul_assoc, hQ, Matrix.one_mul]
      _ = Qᵀ*(R*D*Rᵀ)*R := congrArg (fun A => Qᵀ*A*R) hmarker
      _ = (Qᵀ*R)*D := by
        simp only [Matrix.mul_assoc, hR, Matrix.mul_one]
  have he := congrArg (fun A : Matrix ι ι ℝ => A i j) hcomm
  change (D*(Qᵀ*R)) i j = ((Qᵀ*R)*D) i j at he
  dsimp only [D] at he
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at he
  have hne : c (b i) - c (b j) ≠ 0 := sub_ne_zero.mpr (fun h => hij (hc h))
  have hz : (c (b i)-c (b j))*(Qᵀ*R) i j = 0 := by nlinarith [he]
  exact (mul_eq_zero.mp hz).resolve_left hne

/-- Ordered spectral blocks determine this marker even though their
upper Schur entries vary. This is the independence needed for choosing
angular chart patches without truncating the Gaussian upper entries. -/
theorem realSchurBlockMarker_eq_of_ordered_spectra
    {ι β : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder β]
    (b : ι → β) (c : β → ℝ) (A Q R T U : Matrix ι ι ℝ)
    (hQ : Qᵀ*Q=1) (hR : Rᵀ*R=1)
    (hT : T.BlockTriangular b) (hU : U.BlockTriangular b)
    (hAQ : A=Q*T*Qᵀ) (hAR : A=R*U*Rᵀ)
    (hsep : T.charpoly.Separable)
    (hdiag : ∀ a : β,
      (U.toSquareBlock b a).charpoly = (T.toSquareBlock b a).charpoly) :
    realSchurBlockMarker b c Q = realSchurBlockMarker b c R := by
  apply realSchurBlockMarker_eq_of_offBlock b c Q R hQ hR
  exact realSchurDiagonalSpectralOverlap_offBlock b A Q R T U
    hQ hR hT hU hAQ hAR hsep hdiag

#print axioms blockDiagonal_commute_blockScalar
#print axioms realSchurBlockMarker_eq_of_offBlock
#print axioms realSchurBlockMarker_offBlock_of_eq
#print axioms realSchurBlockMarker_eq_of_ordered_spectra
end SpectralRadiusUpperTail
