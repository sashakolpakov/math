import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.ConstantInverseImageNaturality
import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.InverseImageMap

/-! # Constant Naturality -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.ConstantNaturality

noncomputable section

/-! # Constant-to-de Rham compatibility for actual inverse image

The unchanged original constant inclusion commutes with genuine inverse image
and the actual pullback of the original holomorphic de Rham complex.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace

variable {X Y : Over (Spec (.of ℂ))}

/-- Genuine constant transport in the original nonnegative complexes. -/
def originalConstantComplexInverseImageIsoNat (f : X ⟶ Y) (A : AddCommGrpCat) :
    ((AnalyticInverseImage.originalAnalyticSheafInverseImage f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        ((CochainComplex.single₀ (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf Y)).obj
          ((AlgebraicTopology.Sheaf.Constant.TopCat.constantFunctor (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y))).obj A)) ≅
      (CochainComplex.single₀ (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X)).obj
        ((AlgebraicTopology.Sheaf.Constant.TopCat.constantFunctor (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))).obj A) :=
  (HomologicalComplex.singleMapHomologicalComplex (AnalyticInverseImage.originalAnalyticSheafInverseImage f)
    (ComplexShape.up ℕ) 0).app
      ((AlgebraicTopology.Sheaf.Constant.TopCat.constantFunctor (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y))).obj A) ≪≫
    (CochainComplex.single₀ (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X)).mapIso
      ((AnalyticInverseImage.originalAnalyticConstantInverseImageIso f).app A)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The genuine nonnegative transport has the actual constant-sheaf map in degree zero. -/
theorem originalConstantComplexInverseImageIsoNat_hom_zero (f : X ⟶ Y)
    (A : AddCommGrpCat) :
    (originalConstantComplexInverseImageIsoNat f A).hom.f 0 =
      (AnalyticInverseImage.originalAnalyticConstantInverseImageIso f).hom.app A := by
  unfold originalConstantComplexInverseImageIsoNat
  simp [HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
    HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq]

variable [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The original constant inclusion is natural in genuine inverse image, in every degree. -/
theorem originalDeRhamInverseImagePullbackNat_constants (f : X ⟶ Y) :
    ((AnalyticInverseImage.originalAnalyticSheafInverseImage f).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamComplex Y (Topology.Dimension.Basic.TopologicalSpace.dim Y.left)) ≫
      InverseImageMap.originalDeRhamInverseImagePullbackNat f =
    (originalConstantComplexInverseImageIsoNat f (AddCommGrpCat.of ℂ)).hom ≫
      ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamComplex X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) := by
  ext i
  cases i with
  | zero =>
    change (AnalyticInverseImage.originalAnalyticSheafInverseImage f).map
        (ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamZeroSheaf Y (Topology.Dimension.Basic.TopologicalSpace.dim Y.left)) ≫
      ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat
        (DeRhamPresheafPullback.originalAnalyticSchemeMap f)).homEquiv _ _).symm
          (DeRhamSheafPullback.originalDeRhamSheafPullback f 0) =
      (originalConstantComplexInverseImageIsoNat f (AddCommGrpCat.of ℂ)).hom.f 0 ≫
        ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamZeroSheaf X (Topology.Dimension.Basic.TopologicalSpace.dim X.left)
    rw [originalConstantComplexInverseImageIsoNat_hom_zero]
    let g0 : (TopCat.Sheaf.pullback AddCommGrpCat (DeRhamPresheafPullback.originalAnalyticSchemeMap f)).obj
        (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheaf Y (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) 0) ⟶
      ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheaf X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) 0 :=
      ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat
        (DeRhamPresheafPullback.originalAnalyticSchemeMap f)).homEquiv _ _).symm
          (DeRhamSheafPullback.originalDeRhamSheafPullback f 0)
    let e0 : (TopCat.Sheaf.pullback AddCommGrpCat (DeRhamPresheafPullback.originalAnalyticSchemeMap f)).obj
        ((AlgebraicTopology.Sheaf.Constant.TopCat.constantFunctor (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y))).obj
          (AddCommGrpCat.of ℂ)) ⟶
      (AlgebraicTopology.Sheaf.Constant.TopCat.constantFunctor (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))).obj
        (AddCommGrpCat.of ℂ) :=
      (AnalyticInverseImage.originalAnalyticConstantInverseImageIso f).hom.app (AddCommGrpCat.of ℂ)
    change (TopCat.Sheaf.pullback AddCommGrpCat (DeRhamPresheafPullback.originalAnalyticSchemeMap f)).map
        (ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamZeroSheaf Y (Topology.Dimension.Basic.TopologicalSpace.dim Y.left)) ≫ g0 =
      e0 ≫ ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamZeroSheaf X (Topology.Dimension.Basic.TopologicalSpace.dim X.left)
    apply ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat
      (DeRhamPresheafPullback.originalAnalyticSchemeMap f)).homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
    have hg0 : (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat
        (DeRhamPresheafPullback.originalAnalyticSchemeMap f)).homEquiv _ _ g0 =
      DeRhamSheafPullback.originalDeRhamSheafPullback f 0 := Equiv.apply_symm_apply _ _
    have he0 : (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat
        (DeRhamPresheafPullback.originalAnalyticSchemeMap f)).homEquiv _ _ e0 =
      ConstantPullback.originalConstantSheafPullback f (AddCommGrpCat.of ℂ) :=
      ConstantInverseImageNaturality.originalAnalyticConstantInverseImageIso_homEquiv f (AddCommGrpCat.of ℂ)
    rw [hg0, he0]
    exact ConstantSheafNaturality.originalDeRhamSheafPullback_constants f
  | succ i =>
    exact ((AnalyticInverseImage.originalAnalyticSheafInverseImage f).map_isZero
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0 _ (i + 1)
        (Nat.succ_ne_zero i))).eq_of_src _ _

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.ConstantNaturality
