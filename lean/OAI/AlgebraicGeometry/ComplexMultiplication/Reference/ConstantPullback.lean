import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.DeRhamSheafPullback
import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.AnalyticInverseImage

/-! # Constant Pullback -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.ConstantPullback

noncomputable section

/-! # Actual constant and holomorphic pullbacks

The actual pullback of constant coefficients is the identity on coefficients.
It commutes with the original inclusion of constants as holomorphic zero-forms.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace

variable {X Y : Over (Spec (.of ℂ))}
  [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom]

/-- Original holomorphic-form pullback fixes precisely the original constant zero-forms. -/
theorem originalHolomorphicFormPullback_ofConstant (f : X ⟶ Y)
    (U : Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y))) (c : ℂ) :
    HolomorphicFormPullback.originalHolomorphicFormPullback f U 0 (ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormOfConstant Y (Topology.Dimension.Basic.TopologicalSpace.dim Y.left)
      (Opposite.op U) c) =
    ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormOfConstant X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op (HolomorphicPullback.originalAnalyticPreimage f U)) c := by
  change (ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationKernel X (Topology.Dimension.Basic.TopologicalSpace.dim X.left)
      (Opposite.op (HolomorphicPullback.originalAnalyticPreimage f U)) 0).mkQ
        (HolomorphicPullback.originalKahlerFormPullback f U 0 (Algebra.DeRham.Basic.ofConstant ℂ
          (ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions Y (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) (Opposite.op U)) c)) = _
  rw [HolomorphicPullback.originalKahlerFormPullback, Algebra.DeRham.Basic.map_ofConstant]
  rfl

/-- The actual coefficient identity on constant presheaves under the preimage of opens. -/
def originalConstantPresheafPullback (f : X ⟶ Y) (A : AddCommGrpCat) :
    (AlgebraicTopology.Sheaf.Constant.TopCat.Presheaf.const (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y)) A) ⟶
      (TopCat.Presheaf.pushforward AddCommGrpCat (DeRhamPresheafPullback.originalAnalyticSchemeMap f)).obj
        (AlgebraicTopology.Sheaf.Constant.TopCat.Presheaf.const (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) A) where
  app _ := 𝟙 A
  naturality _ _ _ := rfl

/-- Constants commute with actual zero-form pullback before sheafification. -/
theorem originalDeRhamPresheafPullback_constants (f : X ⟶ Y) :
    ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamZero Y (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) ≫ DeRhamPresheafPullback.originalDeRhamPresheafPullback f 0 =
      originalConstantPresheafPullback f (AddCommGrpCat.of ℂ) ≫
        (TopCat.Presheaf.pushforward AddCommGrpCat (DeRhamPresheafPullback.originalAnalyticSchemeMap f)).map
          (ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamZero X (Topology.Dimension.Basic.TopologicalSpace.dim X.left)) := by
  ext U c
  exact originalHolomorphicFormPullback_ofConstant f U c

/-- The underlying map on the original sheafifications of constant presheaves. -/
def originalConstantSheafPullbackHom (f : X ⟶ Y) (A : AddCommGrpCat) :
    sheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y)))
        (AlgebraicTopology.Sheaf.Constant.TopCat.Presheaf.const (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y)) A) ⟶
      (TopCat.Presheaf.pushforward AddCommGrpCat (DeRhamPresheafPullback.originalAnalyticSchemeMap f)).obj
        (sheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))
          (AlgebraicTopology.Sheaf.Constant.TopCat.Presheaf.const (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) A)) :=
  sheafifyLift (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y)))
    (originalConstantPresheafPullback f A ≫
      (TopCat.Presheaf.pushforward AddCommGrpCat (DeRhamPresheafPullback.originalAnalyticSchemeMap f)).map
        (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))
          (AlgebraicTopology.Sheaf.Constant.TopCat.Presheaf.const (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) A)))
    ((TopCat.Sheaf.pushforward AddCommGrpCat (DeRhamPresheafPullback.originalAnalyticSchemeMap f)).obj
      ((AlgebraicTopology.Sheaf.Constant.TopCat.constantFunctor (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))).obj A)).property

/-- The actual coefficient identity on the original sheafified constants. -/
def originalConstantSheafPullback (f : X ⟶ Y) (A : AddCommGrpCat) :
    (AlgebraicTopology.Sheaf.Constant.TopCat.constantFunctor (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y))).obj A ⟶
      (TopCat.Sheaf.pushforward AddCommGrpCat (DeRhamPresheafPullback.originalAnalyticSchemeMap f)).obj
        ((AlgebraicTopology.Sheaf.Constant.TopCat.constantFunctor (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))).obj A) :=
  ⟨originalConstantSheafPullbackHom f A⟩

omit [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom] in
/-- The actual constant-sheaf pullback extends the precise original coefficient identity. -/
theorem originalConstantSheafPullback_unit (f : X ⟶ Y) (A : AddCommGrpCat) :
    toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y)))
        (AlgebraicTopology.Sheaf.Constant.TopCat.Presheaf.const (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y)) A) ≫
      originalConstantSheafPullbackHom f A =
    originalConstantPresheafPullback f A ≫
      (TopCat.Presheaf.pushforward AddCommGrpCat (DeRhamPresheafPullback.originalAnalyticSchemeMap f)).map
        (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))
          (AlgebraicTopology.Sheaf.Constant.TopCat.Presheaf.const (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) A)) :=
  toSheafify_sheafifyLift _ _ _

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.ConstantPullback
