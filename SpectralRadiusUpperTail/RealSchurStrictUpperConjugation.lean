import SpectralRadiusUpperTail.RealSchurMixedUpperEnergy
import SpectralRadiusUpperTail.RealSchurMixedOrthogonalTransport

namespace SpectralRadiusUpperTail
open scoped Matrix BigOperators

/-- Multiplication by block-diagonal matrices preserves any chosen
block support pattern. -/
theorem blockDiagonal_mul_support
    {ι β : Type*} [Fintype ι] (b : ι → β) (P : β → β → Prop)
    (W T : Matrix ι ι ℝ)
    (hoff : ∀ i j, b i ≠ b j → W i j=0)
    (hT : ∀ i j, ¬P (b i) (b j) → T i j=0) :
    ∀ i j, ¬P (b i) (b j) → (W*T*Wᵀ) i j=0 := by
  classical
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro l _
  by_cases hjl : b j=b l
  · rw [Matrix.mul_apply,Finset.sum_mul]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hik : b i=b k
    · have hk : ¬P (b k) (b l) := by simpa only [← hik,← hjl] using hij
      rw [hT k l hk,mul_zero,zero_mul]
    · rw [hoff i k hik,zero_mul,zero_mul]
  · rw [Matrix.transpose_apply,hoff j l hjl,mul_zero]

def realSchurMixedStrictUpperEmbedLinear {m : ℕ} (s : Fin m → ℕ) :
    (RealSchurMixedStrictUpperEntry s → ℝ) →ₗ[ℝ]
      Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ where
  toFun u := realSchurMixedUpperEntryJoin s 0 u
  map_add' u v := by
    ext i j
    simp only [realSchurMixedUpperEntryJoin,Matrix.add_apply,Pi.add_apply]
    split_ifs <;> simp
  map_smul' a u := by
    ext i j
    simp only [realSchurMixedUpperEntryJoin,Matrix.smul_apply,Pi.smul_apply,smul_eq_mul]
    split_ifs <;> simp

theorem realSchurMixedStrictUpperEmbed_support {m : ℕ} (s : Fin m → ℕ)
    (u : RealSchurMixedStrictUpperEntry s → ℝ)
    (i j : RealSchurMixedCoord s) (h : ¬i.1<j.1) :
    realSchurMixedUpperEntryJoin s 0 u i j=0 := by
  simp [realSchurMixedUpperEntryJoin,h]

theorem realSchurMixedStrictUpper_reconstruct {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hT : ∀ i j, ¬i.1<j.1 → T i j=0) :
    realSchurMixedUpperEntryJoin s 0 (fun p : RealSchurMixedStrictUpperEntry s => T p.1.1 p.1.2)=T := by
  ext i j
  by_cases hij : i.1<j.1
  · simp [realSchurMixedUpperEntryJoin,hij,ne_of_lt hij]
  · simp [realSchurMixedUpperEntryJoin,hij,hT i j hij]

def realSchurMixedStrictUpperConjugationLinear {m : ℕ} (s : Fin m → ℕ)
    (W : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ) :
    (RealSchurMixedStrictUpperEntry s → ℝ) →ₗ[ℝ] (RealSchurMixedStrictUpperEntry s → ℝ) where
  toFun u p := (W*realSchurMixedStrictUpperEmbedLinear s u*Wᵀ) p.1.1 p.1.2
  map_add' u v := by
    ext p
    simp only [map_add,Matrix.mul_add,Matrix.add_mul,Matrix.add_apply,Pi.add_apply]
  map_smul' a u := by
    ext p
    simp only [map_smul,Matrix.mul_smul,Matrix.smul_mul,Matrix.smul_apply,Pi.smul_apply,RingHom.id_apply]

theorem realSchurMixedStrictUpperConjugation_embed
    {m : ℕ} (s : Fin m → ℕ)
    (W : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hoff : ∀ i j : RealSchurMixedCoord s, i.1 ≠ j.1 → W i j=0)
    (u : RealSchurMixedStrictUpperEntry s → ℝ) :
    realSchurMixedUpperEntryJoin s 0 (realSchurMixedStrictUpperConjugationLinear s W u) =
      W*realSchurMixedUpperEntryJoin s 0 u*Wᵀ := by
  exact realSchurMixedStrictUpper_reconstruct s _
    (blockDiagonal_mul_support (fun i : RealSchurMixedCoord s => i.1) (· < ·) W _ hoff
      (realSchurMixedStrictUpperEmbed_support s u))

theorem realSchurMixedStrictUpperConjugation_inverse
    {m : ℕ} (s : Fin m → ℕ)
    (W : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ) (hW : Wᵀ*W=1)
    (hoff : ∀ i j : RealSchurMixedCoord s, i.1 ≠ j.1 → W i j=0)
    (u : RealSchurMixedStrictUpperEntry s → ℝ) :
    realSchurMixedStrictUpperConjugationLinear s Wᵀ
      (realSchurMixedStrictUpperConjugationLinear s W u)=u := by
  have he := realSchurMixedStrictUpperConjugation_embed s W hoff u
  have hc : Wᵀ*(W*realSchurMixedUpperEntryJoin s 0 u*Wᵀ)*Wᵀᵀ =
      realSchurMixedUpperEntryJoin s 0 u := by
    calc
      _ = (Wᵀ*W)*realSchurMixedUpperEntryJoin s 0 u*(Wᵀ*W) := by
        simp only [Matrix.transpose_transpose,Matrix.mul_assoc]
      _ = _ := by simp only [hW,Matrix.one_mul,Matrix.mul_one]
  ext p
  change (Wᵀ*realSchurMixedUpperEntryJoin s 0
    (realSchurMixedStrictUpperConjugationLinear s W u)*Wᵀᵀ) p.1.1 p.1.2=u p
  rw [he,hc]
  simp [realSchurMixedUpperEntryJoin,p.property,ne_of_lt p.property]

#print axioms blockDiagonal_mul_support
#print axioms realSchurMixedStrictUpperConjugation_embed
#print axioms realSchurMixedStrictUpperConjugation_inverse
end SpectralRadiusUpperTail
