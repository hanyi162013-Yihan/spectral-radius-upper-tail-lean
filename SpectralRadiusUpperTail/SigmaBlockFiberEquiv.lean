import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

/-- A fiber of an injectively keyed dependent sum is canonically equivalent
to the corresponding summand. This lets a block matrix have variable-sized
diagonal fibers. -/
def sigmaBlockFiberEquiv {I A : Type*} (F : I → Type*)
    (b : I → A) (hb : Function.Injective b) (i : I) :
    {z : Σ j, F j // b z.1 = b i} ≃ F i where
  toFun z := cast (congrArg F (hb z.2)) z.1.2
  invFun a := ⟨⟨i,a⟩,rfl⟩
  left_inv := by
    rintro ⟨⟨j,v⟩,hj⟩
    have h : j = i := hb hj
    subst j
    rfl
  right_inv _ := rfl

#print axioms sigmaBlockFiberEquiv
end SpectralRadiusUpperTail
