import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RingPushoutTensorComparison
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Affine Cartesian Function Tensor -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.AffineCartesianFunctionTensor.CartesianFunctionTensor

noncomputable section

/-! For an affine Cartesian square, multiplication of the two pulled-back functions gives a bijective tensor map on global sections. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry TensorProduct
universe u
variable {S X Y P : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Y}
    {f : X ⟶ S} {g : Y ⟶ S} (H : IsPullback a b f g)

def left :
    letI := g.appTop.hom.toAlgebra
    letI := (b.appTop.hom.comp g.appTop.hom).toAlgebra
    Γ(Y, ⊤) →ₐ[Γ(S, ⊤)] Γ(P, ⊤) := by
  let := g.appTop.hom.toAlgebra
  let := (b.appTop.hom.comp g.appTop.hom).toAlgebra
  exact { b.appTop.hom with commutes' := fun _ => rfl }

def right :
    letI := f.appTop.hom.toAlgebra
    letI := (b.appTop.hom.comp g.appTop.hom).toAlgebra
    Γ(X, ⊤) →ₐ[Γ(S, ⊤)] Γ(P, ⊤) := by
  let := f.appTop.hom.toAlgebra
  let := (b.appTop.hom.comp g.appTop.hom).toAlgebra
  refine { a.appTop.hom with commutes' := ?_ }
  intro r
  have h := congrArg (fun k : P ⟶ S => k.appTop) H.w
  simp only [Scheme.Hom.comp_appTop] at h
  exact ConcreteCategory.congr_hom h r

def map :=
  letI := g.appTop.hom.toAlgebra
  letI := f.appTop.hom.toAlgebra
  letI := (b.appTop.hom.comp g.appTop.hom).toAlgebra
  Algebra.TensorProduct.lift (left (b := b) (g := g)) (right H) (fun _ _ => .all _ _)

theorem map_tmul (r : Γ(Y, ⊤)) (s : Γ(X, ⊤)) :
    letI := g.appTop.hom.toAlgebra
    letI := f.appTop.hom.toAlgebra
    map H (r ⊗ₜ[Γ(S, ⊤)] s) = b.appTop r * a.appTop s :=
  rfl

theorem map_bijective [IsAffine S] [IsAffine X] [IsAffine Y] :
    Function.Bijective (map H) := by
  let := g.appTop.hom.toAlgebra
  let := f.appTop.hom.toAlgebra
  let := (b.appTop.hom.comp g.appTop.hom).toAlgebra
  exact RingPushoutTensorComparison.tensorLift_bijective_of_isPushout (left (b := b) (g := g)) (right H)
    (isPushout_appTop_of_isPullback H).flip

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.AffineCartesianFunctionTensor.CartesianFunctionTensor
