import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ConstantProductCoordinates

/-! # Constant Product Associativity -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ConstantProductAssociativity.Construction

noncomputable section

/-! The product of two constant families is the usual triple product over the field. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open CartesianMonoidalCategory MonoidalCategory

universe u

variable {K : Type u} [Field K] (A B S : Over (Spec (.of K)))

def constantProductPair : ConstantProductCoordinates.Construction.constantProduct A B S ⟶ A ⊗ B :=
  lift (ConstantProductCoordinates.Construction.constantProductLeft A B S ≫ fst A S) (ConstantProductCoordinates.Construction.constantProductRight A B S ≫ fst B S)

theorem constantProduct_isPullback :
    IsPullback (constantProductPair A B S).left (ConstantProductCoordinates.Construction.constantProductProjection A B S) (A ⊗ B).hom S.hom :=
  AlgebraicGeometry.Quotients.FiniteDescent.ProductBaseLift.Construction.ProductBaseChangeSquare.isPullback A.hom B.hom (ConstantProductCoordinates.Construction.constantLeftBase A S) (ConstantProductCoordinates.Construction.constantRightBase B S)
    (fst A S).left (fst B S).left S.hom
    (IsPullback.of_hasPullback A.hom S.hom) (IsPullback.of_hasPullback B.hom S.hom)

def constantProductAssocIso : ConstantProductCoordinates.Construction.constantProduct A B S ≅ (A ⊗ B) ⊗ S :=
  Over.isoMk (constantProduct_isPullback A B S).isoPullback (by
    rw [← Over.w (snd (A ⊗ B) S), ← Category.assoc]
    exact congrArg (fun m ↦ m ≫ S.hom) (constantProduct_isPullback A B S).isoPullback_hom_snd)

theorem constantProductAssocIso_pair :
    (constantProductAssocIso A B S).hom ≫ fst (A ⊗ B) S = constantProductPair A B S := by
  apply Over.OverMorphism.ext
  exact (constantProduct_isPullback A B S).isoPullback_hom_fst

theorem constantProductAssocIso_base :
    (constantProductAssocIso A B S).hom ≫ snd (A ⊗ B) S = ConstantProductCoordinates.Construction.constantProductBase A B S := by
  apply Over.OverMorphism.ext
  exact (constantProduct_isPullback A B S).isoPullback_hom_snd

theorem constantProductAssocIso_first :
    (constantProductAssocIso A B S).hom ≫ fst (A ⊗ B) S ≫ fst A B =
      ConstantProductCoordinates.Construction.constantProductLeft A B S ≫ fst A S := by
  rw [← Category.assoc, constantProductAssocIso_pair]
  exact lift_fst _ _

theorem constantProductAssocIso_second :
    (constantProductAssocIso A B S).hom ≫ fst (A ⊗ B) S ≫ snd A B =
      ConstantProductCoordinates.Construction.constantProductRight A B S ≫ fst B S := by
  rw [← Category.assoc, constantProductAssocIso_pair]
  exact lift_snd _ _

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ConstantProductAssociativity.Construction
