import OAI.AlgebraicGeometry.Comparison.Betti.SectionsPullbackNormalization

/-! # Constant Image Sections -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ConstantImageSections

noncomputable section

/-! The adjoint coefficient map induces exactly the original map on top-open sections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

variable {X Y : TopCat.{0}} (f : Y ⟶ X)
  {A : ConstantSheafSections.ComplexSheaves X} {B : ConstantSheafSections.ComplexSheaves Y}
  (α : A ⟶ (TopologicalSheafPullback.sheafDirectImage f).obj B)

theorem constantHomSectionsLinearEquiv_directImage
    (g : ConstantSheafSections.standardConstantSheaf X ⟶ A) :
    ConstantSheafSections.constantHomSectionsLinearEquiv B
      ((TopologicalSheafPullback.constantPullbackIso f).inv ≫ (TopologicalSheafPullback.sheafInverseImage f).map g ≫
        ((TopologicalSheafPullback.sheafImageAdjunction f).homEquiv A B).symm α) =
      α.hom.app (op ⊤) (ConstantSheafSections.constantHomSectionsLinearEquiv A g) := by
  let β := ((TopologicalSheafPullback.sheafImageAdjunction f).homEquiv A B).symm α
  have hn := ConstantSheafSections.constantHomSectionsLinearEquiv_naturality
    ((TopologicalSheafPullback.constantPullbackIso f).inv ≫ (TopologicalSheafPullback.sheafInverseImage f).map g) β
  have hp := SectionsPullbackNormalization.constantHomSectionsLinearEquiv_pullback f A g
  have hα : (TopologicalSheafPullback.sheafImageAdjunction f).unit.app A ≫ (TopologicalSheafPullback.sheafDirectImage f).map β = α :=
    ((TopologicalSheafPullback.sheafImageAdjunction f).homEquiv A B).apply_symm_apply α
  have hs := ConcreteCategory.congr_hom
    (congrArg (fun k => k.hom.app (op ⊤)) hα) (ConstantSheafSections.constantHomSectionsLinearEquiv A g)
  exact (congrArg (ConstantSheafSections.constantHomSectionsLinearEquiv B) (Category.assoc _ _ _).symm).trans
    (hn.trans ((congrArg (β.hom.app (op ⊤)) hp).trans hs))

end

end OAI.AlgebraicGeometry.Comparison.Betti.ConstantImageSections
