import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Universal.Line
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Product.LineNormalization

/-! # Normalization -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient

noncomputable section

/-! Normalize the actual descended line along the group origin while
retaining an isomorphism with the original rigidified line after pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme.{0}} {A B Q : Over S} [GrpObj A]
  (D : Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine A B) (hΓ : GlobalFunctions.Construction.HasUniversalGlobalFunctions A) (q : B ⟶ Q)
  (H : ∀ {T : Over S} (a b : T ⟶ B),
    a ≫ q = b ≫ q → D.relativeValue a = D.relativeValue b)
  [IsAffineHom (q ⊗ₘ 𝟙 A).left] [Flat (q ⊗ₘ 𝟙 A).left]
  [Surjective (q ⊗ₘ 𝟙 A).left]

def Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine.universalNormalizedQuotientLine : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (Q ⊗ A).left :=
  FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductBundle A Q (D.universalQuotientLine hΓ q H)

def Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine.universalNormalizedQuotientLine_axis :
    (Scheme.Modules.pullback (lift (𝟙 Q) (1 : Q ⟶ A)).left).obj
      (D.universalNormalizedQuotientLine hΓ q H).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Q.left :=
  FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductBundle_axis A Q (D.universalQuotientLine hΓ q H)

theorem Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine.universalNormalizedQuotientLine_pullback_class :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (q ⊗ₘ 𝟙 A).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.universalNormalizedQuotientLine hΓ q H)) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.bundle := by
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (q ⊗ₘ 𝟙 A).left
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductBundle A Q (D.universalQuotientLine hΓ q H))) = _
  rw [FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductBundle_class, FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductClass_pullback]
  have h : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (q ⊗ₘ 𝟙 A).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.universalQuotientLine hΓ q H)) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.bundle :=
    Quotient.sound ⟨D.universalQuotientLinePullbackIso hΓ q H⟩
  rw [h]
  exact FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductClass_of_axis A B (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.bundle)
    (Quotient.sound ⟨D.axis⟩)

def Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine.universalNormalizedQuotientLinePullbackIso :
    (Scheme.Modules.pullback (q ⊗ₘ 𝟙 A).left).obj
      (D.universalNormalizedQuotientLine hΓ q H).sheaf ≅ D.bundle.sheaf :=
  Classical.choice (Quotient.exact (D.universalNormalizedQuotientLine_pullback_class hΓ q H))

def Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine.universalRigidifiedQuotientLine : Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine A Q where
  bundle := D.universalNormalizedQuotientLine hΓ q H
  axis := D.universalNormalizedQuotientLine_axis hΓ q H

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient
