import OAI.RepresentationTheory.Theta.Geometric.ProductFiberMaps

/-! # Product Fiber Naturality -/

namespace OAI.RepresentationTheory.Theta.Geometric.ProductFiberNaturality

noncomputable section

/-! Naturality of the actual map from a product of geometric fibers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

theorem productFiberMap_naturality {S T : Scheme.{u}} {A A' B B' : Over S}
    (f : A ⟶ A') (g : B ⟶ B') (z : T ⟶ S) :
    ProductFiberMaps.productFiberMap A B z ≫ (f ⊗ₘ g).left =
      ((Over.pullback z).map f ⊗ₘ (Over.pullback z).map g).left ≫ ProductFiberMaps.productFiberMap A' B' z := by
  have hn := congrArg Over.Hom.left (Functor.LaxMonoidal.μ_natural (Over.pullback z) f g)
  have hp : ((Over.pullback z).map (f ⊗ₘ g)).left ≫ Limits.pullback.fst (A' ⊗ B').hom z =
      Limits.pullback.fst (A ⊗ B).hom z ≫ (f ⊗ₘ g).left := Limits.pullback.lift_fst _ _ _
  change ((Functor.Monoidal.μIso (Over.pullback z) A B).hom.left ≫
      Limits.pullback.fst (A ⊗ B).hom z) ≫ (f ⊗ₘ g).left =
    ((Over.pullback z).map f ⊗ₘ (Over.pullback z).map g).left ≫
      (Functor.Monoidal.μIso (Over.pullback z) A' B').hom.left ≫
        Limits.pullback.fst (A' ⊗ B').hom z
  rw [Category.assoc, ← hp, ← Category.assoc]
  exact congrArg (fun a => a ≫ Limits.pullback.fst (A' ⊗ B').hom z) hn.symm

end

end OAI.RepresentationTheory.Theta.Geometric.ProductFiberNaturality
