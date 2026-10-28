import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ConstantFamilyPointFiber

/-! # Constant Product Point Fiber -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ConstantProductPointFiber.Construction

noncomputable section

/-! The Cartesian fiber of a product of constant families at a rational base point. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open CartesianMonoidalCategory MonoidalCategory

universe u

variable {K : Type u} [Field K] (A B S : Over (Spec (.of K)))
variable (s : 𝟙_ (Over (Spec (.of K))) ⟶ S)

def constantProductPointFiberMap : (A ⊗ B).left ⟶ (ConstantProductCoordinates.Construction.constantProduct A B S).left :=
  AlgebraicGeometry.Quotients.FiniteDescent.ProductBaseLift.Construction.ProductBaseChangeSquare.map (ConstantProductCoordinates.Construction.constantLeftBase A S) (ConstantProductCoordinates.Construction.constantRightBase B S) A.hom B.hom
    (ConstantFamilyPointFiber.Construction.constantFamilyPointFiber A S s).left (ConstantFamilyPointFiber.Construction.constantFamilyPointFiber B S s).left s.left
    (ConstantFamilyPointFiber.Construction.constantFamilyPointFiber_isPullback A S s) (ConstantFamilyPointFiber.Construction.constantFamilyPointFiber_isPullback B S s)

theorem constantProductPointFiberMap_isPullback :
    IsPullback (constantProductPointFiberMap A B S s) (A ⊗ B).hom
      (ConstantProductCoordinates.Construction.constantProductProjection A B S) s.left :=
  AlgebraicGeometry.Quotients.FiniteDescent.ProductBaseLift.Construction.ProductBaseChangeSquare.isPullback (ConstantProductCoordinates.Construction.constantLeftBase A S) (ConstantProductCoordinates.Construction.constantRightBase B S) A.hom B.hom
    (ConstantFamilyPointFiber.Construction.constantFamilyPointFiber A S s).left (ConstantFamilyPointFiber.Construction.constantFamilyPointFiber B S s).left s.left
    (ConstantFamilyPointFiber.Construction.constantFamilyPointFiber_isPullback A S s) (ConstantFamilyPointFiber.Construction.constantFamilyPointFiber_isPullback B S s)

def constantProductPointFiber : A ⊗ B ⟶ ConstantProductCoordinates.Construction.constantProduct A B S :=
  Over.homMk (constantProductPointFiberMap A B S s) (by
    have h := (constantProductPointFiberMap_isPullback A B S s).w
    have hs : s.left ≫ S.hom = 𝟙 _ := Over.w s
    change constantProductPointFiberMap A B S s ≫ (ConstantProductCoordinates.Construction.constantProductProjection A B S ≫ S.hom) = _
    exact (Category.assoc _ _ _).symm.trans ((congrArg (fun m ↦ m ≫ S.hom) h).trans
      ((Category.assoc _ _ _).trans ((congrArg (fun m ↦ (A ⊗ B).hom ≫ m) hs).trans (Category.comp_id _)))))

theorem constantProductPointFiber_base :
    constantProductPointFiber A B S s ≫ ConstantProductCoordinates.Construction.constantProductBase A B S = toUnit (A ⊗ B) ≫ s := by
  apply Over.OverMorphism.ext
  exact (constantProductPointFiberMap_isPullback A B S s).w

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ConstantProductPointFiber.Construction
