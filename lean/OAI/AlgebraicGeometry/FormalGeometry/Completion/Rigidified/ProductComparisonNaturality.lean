import OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified.ProductLine

/-! # Product Comparison Naturality -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified

noncomputable section

/-! Canonical normalized comparisons on a product family commute with
every change of parameter, including nonreduced test schemes. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u
variable {K : Type u} [Field K] {A B : Over (Spec (.of K))} [GrpObj A]
  (D : ProductLine.Construction.RigidifiedProductLine A B)

omit [GrpObj A] in
theorem ProductLine.Construction.RigidifiedProductLine.parameterMap_comp {T U : Over (Spec (.of K))} (j : U ⟶ T) (a : T ⟶ B) :
    (j ⊗ₘ 𝟙 A).left ≫ (a ⊗ₘ 𝟙 A).left = ((j ≫ a) ⊗ₘ 𝟙 A).left := by
  have h : (j ⊗ₘ 𝟙 A) ≫ (a ⊗ₘ 𝟙 A) = (j ≫ a) ⊗ₘ 𝟙 A := by simp
  exact congrArg Over.Hom.left h

theorem ProductLine.Construction.RigidifiedProductLine.line_class_pullback {T U : Over (Spec (.of K))} (j : U ⟶ T) (a : T ⟶ B) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (j ⊗ₘ 𝟙 A).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.line a)) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.line (j ≫ a)) := by
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (j ⊗ₘ 𝟙 A).left
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (a ⊗ₘ 𝟙 A).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.bundle)) = _
  rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, ProductLine.Construction.RigidifiedProductLine.parameterMap_comp]
  rfl

def ProductLine.Construction.RigidifiedProductLine.pullbackComparison {T U : Over (Spec (.of K))} (j : U ⟶ T) (a b : T ⟶ B)
    (e : (D.line a).sheaf ≅ (D.line b).sheaf) :
    (D.line (j ≫ a)).sheaf ≅ (D.line (j ≫ b)).sheaf :=
  IsoPullback.Construction.lineIsoPullbackTo (a ⊗ₘ 𝟙 A).left (b ⊗ₘ 𝟙 A).left (j ⊗ₘ 𝟙 A).left
    ((j ≫ a) ⊗ₘ 𝟙 A).left ((j ≫ b) ⊗ₘ 𝟙 A).left
    (ProductLine.Construction.RigidifiedProductLine.parameterMap_comp j a) (ProductLine.Construction.RigidifiedProductLine.parameterMap_comp j b) D.bundle.sheaf e

theorem ProductLine.Construction.RigidifiedProductLine.pullbackComparison_normalized {T U : Over (Spec (.of K))} (j : U ⟶ T) (a b : T ⟶ B)
    (e : (D.line a).sheaf ≅ (D.line b).sheaf) (he : D.Normalized a b e) :
    D.Normalized (j ≫ a) (j ≫ b) (D.pullbackComparison j a b e) :=
  IsoPullback.Construction.lineIsoPullbackTo_normalized (a ⊗ₘ 𝟙 A).left (b ⊗ₘ 𝟙 A).left (j ⊗ₘ 𝟙 A).left
    ((j ≫ a) ⊗ₘ 𝟙 A).left ((j ≫ b) ⊗ₘ 𝟙 A).left
    (ProductLine.Construction.RigidifiedProductLine.parameterMap_comp j a) (ProductLine.Construction.RigidifiedProductLine.parameterMap_comp j b)
    (lift (𝟙 B) (1 : B ⟶ A)).left (lift (𝟙 T) (1 : T ⟶ A)).left
    a.left b.left (lift (𝟙 U) (1 : U ⟶ A)).left j.left
    (ProductLine.Construction.RigidifiedProductLine.axis_square j) (ProductLine.Construction.RigidifiedProductLine.axis_square a) (ProductLine.Construction.RigidifiedProductLine.axis_square b) (ProductLine.Construction.RigidifiedProductLine.axis_square (j ≫ a)) (ProductLine.Construction.RigidifiedProductLine.axis_square (j ≫ b))
    D.bundle.sheaf D.axis e he

variable [IsAlgClosed K] [IsProper A.hom] [IsIntegral A.left]

theorem ProductLine.Construction.RigidifiedProductLine.comparison_pullback {T U : Over (Spec (.of K))} (j : U ⟶ T) (a b : T ⟶ B)
    (h : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.line a) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.line b))
    (h' : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.line (j ≫ a)) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.line (j ≫ b))) :
    D.pullbackComparison j a b (D.comparison a b h) = D.comparison (j ≫ a) (j ≫ b) h' :=
  D.comparison_unique (j ≫ a) (j ≫ b) h' _
    (D.pullbackComparison_normalized j a b _ (D.comparison_normalized a b h))

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified
