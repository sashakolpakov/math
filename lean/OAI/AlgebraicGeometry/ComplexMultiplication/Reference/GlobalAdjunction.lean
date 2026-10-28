import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.GlobalPullback
import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.InverseImageMap

/-! # Global Adjunction -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.GlobalAdjunction

noncomputable section

/-! # Global sections of an adjointed actual complex morphism

For the actual scheme-point map, adjunction-unit pullback followed by the
adjointed morphism is the original pushforward morphism on the top open.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint

variable {X Y : Over (Spec (.of ℂ))}

/-- Evaluation on the top open of an actual pushforward complex morphism. -/
def originalPushforwardGlobalComplexMap (f : X ⟶ Y) {ι : Type*} (c : ComplexShape ι)
    (K : HomologicalComplex (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf Y) c)
    (L : HomologicalComplex (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) c)
    (g : K ⟶ ((TopCat.Sheaf.pushforward AddCommGrpCat
      (DeRhamPresheafPullback.originalAnalyticSchemeMap f)).mapHomologicalComplex c).obj L) :
    ((AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y))).mapHomologicalComplex c).obj K ⟶
    ((AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))).mapHomologicalComplex c).obj L where
  f i := (g.f i).hom.app (Opposite.op ⊤)
  comm' i j _ := congrArg (fun q ↦ q.hom.app (Opposite.op ⊤)) (g.comm i j)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Actual global pullback agrees with the original morphism on the top open. -/
theorem originalGlobalComplexInverseImage_adjunction (f : X ⟶ Y) {ι : Type*}
    (c : ComplexShape ι) (K : HomologicalComplex (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf Y) c)
    (L : HomologicalComplex (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) c)
    (g : K ⟶ ((TopCat.Sheaf.pushforward AddCommGrpCat
      (DeRhamPresheafPullback.originalAnalyticSchemeMap f)).mapHomologicalComplex c).obj L) :
    (NatTrans.mapHomologicalComplex (GlobalSheafPullback.originalGlobalSectionsInverseImageNat f) c).app K ≫
      ((AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))).mapHomologicalComplex c).map
          (InverseImageMap.originalInverseImageComplexMap f c K L g) =
    originalPushforwardGlobalComplexMap f c K L g := by
  refine HomologicalComplex.hom_ext _ _ (fun i ↦ ?_)
  have h := ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat
    (DeRhamPresheafPullback.originalAnalyticSchemeMap f)).homEquiv (K.X i) (L.X i)).apply_symm_apply (g.f i)
  exact congrArg (fun q ↦ q.hom.app (Opposite.op ⊤)) h

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.GlobalAdjunction
