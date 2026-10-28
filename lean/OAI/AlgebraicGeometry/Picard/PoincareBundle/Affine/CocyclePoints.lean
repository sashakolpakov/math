import OAI.AlgebraicGeometry.Picard.PoincareBundle.CocyclePointEvaluation
import Mathlib.AlgebraicGeometry.Group.Affine

/-! # Cocycle Points -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.CocyclePoints

noncomputable section

/-! Affine algebra points preserve the actual group multiplication and change of test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.CocyclePointEvaluation WithConv

variable (k R S : Type u) [CommRing k] [CommRing R] [Bialgebra k R] [CommRing S] [Algebra k S]

theorem product_toConv (x y : R →ₐ[k] S) :
    toConv (CocyclePointEvaluation.product k R S x y) = toConv x * toConv y := by
  apply WithConv.ext
  apply AlgHom.ext
  intro a
  exact (AlgHom.convMul_apply (toConv x) (toConv y) a).symm

/-- The actual spectrum point associated with an algebra homomorphism. -/
def point (x : R →ₐ[k] S) :
    (Spec (.of S)).asOver (Spec (.of k)) ⟶ (Spec (.of R)).asOver (Spec (.of k)) :=
  Spec.mapMulEquiv (toConv x)

theorem point_mul (x y : R →ₐ[k] S) :
    point k R S (CocyclePointEvaluation.product k R S x y) = point k R S x * point k R S y := by
  exact (congrArg (Spec.mapMulEquiv (R := k) (S := R) (T := S)) (product_toConv k R S x y)).trans
    ((Spec.mapMulEquiv (R := k) (S := R) (T := S)).map_mul _ _)

theorem point_one :
    point k R S ((Algebra.ofId k S).comp (Bialgebra.counitAlgHom k R)) = 1 :=
  (Spec.mapMulEquiv (R := k) (S := R) (T := S)).map_one

theorem point_natural {T : Type u} [CommRing T] [Algebra k T] (f : S →ₐ[k] T) (x : R →ₐ[k] S) :
    ((Spec.map (CommRingCat.ofHom f.toRingHom)).asOver (Spec (.of k))) ≫ point k R S x =
      point k R T (f.comp x) := by
  apply Over.OverMorphism.ext
  exact (Spec.map_comp (CommRingCat.ofHom x.toRingHom) (CommRingCat.ofHom f.toRingHom)).symm

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.CocyclePoints
