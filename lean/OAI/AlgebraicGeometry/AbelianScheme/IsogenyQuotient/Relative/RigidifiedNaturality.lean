import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.RigidifiedLine

/-! # Rigidified Naturality -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative

noncomputable section

/-! Relative normalized comparisons preserve the actual section
frame under pullback. Their canonical choices agree on Noetherian parameters. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] (D : RigidifiedLine.Construction.RelativeRigidifiedProductLine A B)

omit [GrpObj A] in
theorem RigidifiedLine.Construction.RelativeRigidifiedProductLine.parameterMap_comp {T U : Over S} (j : U ⟶ T) (a : T ⟶ B) :
    (j ⊗ₘ 𝟙 A).left ≫ (a ⊗ₘ 𝟙 A).left = ((j ≫ a) ⊗ₘ 𝟙 A).left := by
  have h : (j ⊗ₘ 𝟙 A) ≫ (a ⊗ₘ 𝟙 A) = (j ≫ a) ⊗ₘ 𝟙 A := by simp
  exact congrArg Over.Hom.left h

theorem RigidifiedLine.Construction.RelativeRigidifiedProductLine.line_class_pullback {T U : Over S} (j : U ⟶ T) (a : T ⟶ B) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (j ⊗ₘ 𝟙 A).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.line a)) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.line (j ≫ a)) := by
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (j ⊗ₘ 𝟙 A).left
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (a ⊗ₘ 𝟙 A).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.bundle)) = _
  rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, RigidifiedLine.Construction.RelativeRigidifiedProductLine.parameterMap_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem RigidifiedLine.Construction.RelativeRigidifiedProductLine.relativeValue_natural {T U : Over S} (j : U ⟶ T) (a : T ⟶ B) :
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A).obj.map j.op (D.relativeValue a) = D.relativeValue (j ≫ a) := by
  let c : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A).obj (op T) := AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.line a)
  have hn := (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).naturality_apply j.op c
  exact hn.symm.trans (congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (op U)) (D.line_class_pullback j a))

def RigidifiedLine.Construction.RelativeRigidifiedProductLine.pullbackComparison {T U : Over S} (j : U ⟶ T) (a b : T ⟶ B)
    (e : (D.line a).sheaf ≅ (D.line b).sheaf) :
    (D.line (j ≫ a)).sheaf ≅ (D.line (j ≫ b)).sheaf :=
  FormalGeometry.Completion.Rigidified.IsoPullback.Construction.lineIsoPullbackTo (a ⊗ₘ 𝟙 A).left (b ⊗ₘ 𝟙 A).left (j ⊗ₘ 𝟙 A).left
    ((j ≫ a) ⊗ₘ 𝟙 A).left ((j ≫ b) ⊗ₘ 𝟙 A).left
    (RigidifiedLine.Construction.RelativeRigidifiedProductLine.parameterMap_comp j a) (RigidifiedLine.Construction.RelativeRigidifiedProductLine.parameterMap_comp j b) D.bundle.sheaf e

theorem RigidifiedLine.Construction.RelativeRigidifiedProductLine.pullbackComparison_normalized {T U : Over S} (j : U ⟶ T) (a b : T ⟶ B)
    (e : (D.line a).sheaf ≅ (D.line b).sheaf) (he : D.Normalized a b e) :
    D.Normalized (j ≫ a) (j ≫ b) (D.pullbackComparison j a b e) :=
  FormalGeometry.Completion.Rigidified.IsoPullback.Construction.lineIsoPullbackTo_normalized (a ⊗ₘ 𝟙 A).left (b ⊗ₘ 𝟙 A).left (j ⊗ₘ 𝟙 A).left
    ((j ≫ a) ⊗ₘ 𝟙 A).left ((j ≫ b) ⊗ₘ 𝟙 A).left
    (RigidifiedLine.Construction.RelativeRigidifiedProductLine.parameterMap_comp j a) (RigidifiedLine.Construction.RelativeRigidifiedProductLine.parameterMap_comp j b)
    (lift (𝟙 B) (1 : B ⟶ A)).left (lift (𝟙 T) (1 : T ⟶ A)).left
    a.left b.left (lift (𝟙 U) (1 : U ⟶ A)).left j.left
    (RigidifiedLine.Construction.RelativeRigidifiedProductLine.axis_square j) (RigidifiedLine.Construction.RelativeRigidifiedProductLine.axis_square a) (RigidifiedLine.Construction.RelativeRigidifiedProductLine.axis_square b) (RigidifiedLine.Construction.RelativeRigidifiedProductLine.axis_square (j ≫ a)) (RigidifiedLine.Construction.RelativeRigidifiedProductLine.axis_square (j ≫ b))
    D.bundle.sheaf D.axis e he

variable [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]

theorem RigidifiedLine.Construction.RelativeRigidifiedProductLine.comparison_pullback {T U : Over S} [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left]
    (j : U ⟶ T) (a b : T ⟶ B) (h : D.relativeValue a = D.relativeValue b)
    (h' : D.relativeValue (j ≫ a) = D.relativeValue (j ≫ b)) :
    D.pullbackComparison j a b (D.comparison a b h) = D.comparison (j ≫ a) (j ≫ b) h' :=
  D.comparison_unique (j ≫ a) (j ≫ b) h' _
    (D.pullbackComparison_normalized j a b _ (D.comparison_normalized a b h))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative
