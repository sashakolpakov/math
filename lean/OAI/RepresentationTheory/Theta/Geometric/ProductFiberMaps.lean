import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes

/-! # Product Fiber Maps -/

namespace OAI.RepresentationTheory.Theta.Geometric.ProductFiberMaps

noncomputable section

/-! Native projection and multiplication equations for the product of
two base changes of a group scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u
variable {S T : Scheme.{u}}

local instance productFiberGroup (A : Over S) [GrpObj A] (z : T ⟶ S) :
    GrpObj ((Over.pullback z).obj A) := Functor.grpObjObj

def productFiberMap (A B : Over S) (z : T ⟶ S) :
    ((Over.pullback z).obj A ⊗ (Over.pullback z).obj B).left ⟶ (A ⊗ B).left :=
  (Functor.Monoidal.μIso (Over.pullback z) A B).hom.left ≫
    Limits.pullback.fst (A ⊗ B).hom z

theorem productFiberMap_fst (A B : Over S) (z : T ⟶ S) :
    productFiberMap A B z ≫ (fst A B).left =
      (fst ((Over.pullback z).obj A) ((Over.pullback z).obj B)).left ≫
        Limits.pullback.fst A.hom z := by
  exact (Category.assoc _ _ _).trans (Over.μ_pullback_left_fst_fst A B)

theorem productFiberMap_snd (A B : Over S) (z : T ⟶ S) :
    productFiberMap A B z ≫ (snd A B).left =
      (snd ((Over.pullback z).obj A) ((Over.pullback z).obj B)).left ≫
        Limits.pullback.fst B.hom z := by
  exact (Category.assoc _ _ _).trans (Over.μ_pullback_left_fst_snd A B)

theorem productFiberMap_mul (A : Over S) [GrpObj A] (z : T ⟶ S) :
    productFiberMap A A z ≫ μ[A].left =
      μ[(Over.pullback z).obj A].left ≫ Limits.pullback.fst A.hom z := by
  have h : ((Over.pullback z).map μ[A]).left ≫ Limits.pullback.fst A.hom z =
      Limits.pullback.fst (A ⊗ A).hom z ≫ μ[A].left := Limits.pullback.lift_fst _ _ _
  change (Functor.Monoidal.μIso (Over.pullback z) A A).hom.left ≫
      Limits.pullback.fst (A ⊗ A).hom z ≫ μ[A].left =
    ((Functor.Monoidal.μIso (Over.pullback z) A A).hom.left ≫
      ((Over.pullback z).map μ[A]).left) ≫ Limits.pullback.fst A.hom z
  rw [Category.assoc, h]

end

end OAI.RepresentationTheory.Theta.Geometric.ProductFiberMaps
