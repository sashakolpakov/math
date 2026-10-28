import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.Line
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Product.LineNormalization

/-! # Normalization -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative

noncomputable section

/-! Normalize the actual descended line along the group origin while
retaining an isomorphism with the original rigidified line after pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme.{0}} {A B Q : Over S} [GrpObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]
  (D : RigidifiedLine.Construction.RelativeRigidifiedProductLine A B) (q : B ⟶ Q)
  (H : ∀ {T : Over S} [IsLocallyNoetherian T.left] (a b : T ⟶ B),
    a ≫ q = b ≫ q → D.relativeValue a = D.relativeValue b)
  [IsAffineHom (q ⊗ₘ 𝟙 A).left] [Flat (q ⊗ₘ 𝟙 A).left]
  [Surjective (q ⊗ₘ 𝟙 A).left] [LocallyOfFinitePresentation (q ⊗ₘ 𝟙 A).left]
  [IsLocallyNoetherian (Q ⊗ A).left]

def RigidifiedLine.Construction.RelativeRigidifiedProductLine.normalizedQuotientLine : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (Q ⊗ A).left :=
  FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductBundle A Q (D.quotientLine q H)

def RigidifiedLine.Construction.RelativeRigidifiedProductLine.normalizedQuotientLine_axis :
    (Scheme.Modules.pullback (lift (𝟙 Q) (1 : Q ⟶ A)).left).obj
      (D.normalizedQuotientLine q H).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Q.left :=
  FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductBundle_axis A Q (D.quotientLine q H)

theorem RigidifiedLine.Construction.RelativeRigidifiedProductLine.normalizedQuotientLine_pullback_class :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (q ⊗ₘ 𝟙 A).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.normalizedQuotientLine q H)) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.bundle := by
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (q ⊗ₘ 𝟙 A).left
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductBundle A Q (D.quotientLine q H))) = _
  rw [FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductBundle_class, FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductClass_pullback]
  have h : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (q ⊗ₘ 𝟙 A).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.quotientLine q H)) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.bundle :=
    Quotient.sound ⟨D.quotientLinePullbackIso q H⟩
  rw [h]
  exact FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductClass_of_axis A B (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.bundle)
    (Quotient.sound ⟨D.axis⟩)

def RigidifiedLine.Construction.RelativeRigidifiedProductLine.normalizedQuotientLinePullbackIso :
    (Scheme.Modules.pullback (q ⊗ₘ 𝟙 A).left).obj
      (D.normalizedQuotientLine q H).sheaf ≅ D.bundle.sheaf :=
  Classical.choice (Quotient.exact (D.normalizedQuotientLine_pullback_class q H))

def RigidifiedLine.Construction.RelativeRigidifiedProductLine.rigidifiedQuotientLine : RigidifiedLine.Construction.RelativeRigidifiedProductLine A Q where
  bundle := D.normalizedQuotientLine q H
  axis := D.normalizedQuotientLine_axis q H

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative
