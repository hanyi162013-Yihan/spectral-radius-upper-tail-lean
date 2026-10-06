import SpectralRadiusUpperTail.RealRootRankUniqueness
import SpectralRadiusUpperTail.MarkedRealTwoBlockRootBranch
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open Polynomial Set
open scoped Matrix

/-- Rank among real roots is an upper-matrix condition, so each rank
still leaves the angular domain as an independent product factor. -/
def markedRealUpperRankSource (m k : ℕ) (b : ℝ) :
    Set (realSchurMixedUpperSubmodule (markedRealTwoBlockSizes m)) :=
  {S | S.val.charpoly.Separable ∧ b < markedRealScalar m S.val ∧
    realPolynomialRootRank S.val.charpoly (markedRealScalar m S.val) = k}

/-- The simple upper matrices split into countably many real-root ranks. -/
theorem markedRealUpperSimpleSource_eq_iUnion_rank
    (m : ℕ) (b : ℝ) :
    markedRealUpperSimpleSource m b =
      ⋃ k : ℕ, markedRealUpperRankSource m k b := by
  ext S
  simp only [markedRealUpperSimpleSource, markedRealUpperRankSource,
    Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · intro h
    exact ⟨realPolynomialRootRank S.val.charpoly
      (markedRealScalar m S.val), h.1, h.2, rfl⟩
  · rintro ⟨k, hsep, hb, _⟩
    exact ⟨hsep, hb⟩

/-- A marked upper matrix belongs to only one real-root-rank layer. -/
theorem markedRealUpperRankSource_unique
    (m k l : ℕ) (b : ℝ)
    (S : realSchurMixedUpperSubmodule (markedRealTwoBlockSizes m))
    (hk : S ∈ markedRealUpperRankSource m k b)
    (hl : S ∈ markedRealUpperRankSource m l b) : k = l := by
  exact hk.2.2.symm.trans hl.2.2

/-- The scalar block of an upper matrix is a root of its full
characteristic polynomial. -/
theorem markedRealUpper_scalar_isRoot
    (m : ℕ) (hm : 0 < m)
    (S : realSchurMixedUpperSubmodule (markedRealTwoBlockSizes m)) :
    S.val.charpoly.IsRoot (markedRealScalar m S.val) := by
  have hfactor := markedRealTwoBlock_charpoly_factor m hm S.val 1
    S.property (by simp)
  simp only [Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one] at hfactor
  rw [Polynomial.IsRoot, hfactor, Polynomial.eval_mul,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  simp

/-- On one fixed real-root rank, even the unmarked matrix map is
injective on the independent angular/upper product. -/
theorem markedRealAngular_matrixMap_injOn_rank
    (m k : ℕ) (hm : 0 < m) (b : ℝ) :
    InjOn (fun p => (markedRealAngularProductMap m p).1)
      (markedRealAngularPositiveSource m ×ˢ
        markedRealUpperRankSource m k b) := by
  intro p hp q hq heq
  rcases p with ⟨w,S⟩
  rcases q with ⟨v,T⟩
  have hw := hp.1.1
  have hv := hq.1.1
  have hwpos := hp.1.2
  have hvpos := hq.1.2
  have hsepS := hp.2.1
  have hrankS := hp.2.2.2
  have hrankT := hq.2.2.2
  have hmat :
      (realSchurMixedAngularFrame (markedRealTwoBlockSizes m) w) * S.val *
        (realSchurMixedAngularFrame (markedRealTwoBlockSizes m) w)ᵀ =
      (realSchurMixedAngularFrame (markedRealTwoBlockSizes m) v) * T.val *
        (realSchurMixedAngularFrame (markedRealTwoBlockSizes m) v)ᵀ := heq
  have hpoly : S.val.charpoly = T.val.charpoly := by
    have h := congrArg Matrix.charpoly hmat
    simpa only [realMatrixOrthogonalConjugation_charpoly _ _ _
      (realSchurMixedAngularFrame_orthogonal _ _)] using h
  have hscalar : markedRealScalar m S.val = markedRealScalar m T.val := by
    apply realPolynomialRootRank_injective_on_roots S.val.charpoly
      S.val.charpoly_monic.ne_zero
      (markedRealScalar m S.val) (markedRealScalar m T.val)
      (markedRealUpper_scalar_isRoot m hm S)
      (hpoly ▸ markedRealUpper_scalar_isRoot m hm T)
    rw [hrankS, hpoly, hrankT]
  have hsep : ((realSchurMixedAngularFrame
      (markedRealTwoBlockSizes m) w) * S.val *
      (realSchurMixedAngularFrame (markedRealTwoBlockSizes m) w)ᵀ).charpoly.Separable := by
    rw [realMatrixOrthogonalConjugation_charpoly _ _ _
      (realSchurMixedAngularFrame_orthogonal _ w)]
    exact hsepS
  obtain ⟨hwv,hST⟩ := markedRealAngular_upperProduct_injective_at_root
    m w v S.val T.val hw hv hwpos hvpos S.property T.property
      hscalar hmat hsep
  exact Prod.ext hwv (Subtype.ext hST)

#print axioms markedRealAngular_matrixMap_injOn_rank
end SpectralRadiusUpperTail
