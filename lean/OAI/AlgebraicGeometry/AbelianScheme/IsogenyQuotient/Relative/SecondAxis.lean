import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.Normalization

/-! # Second Axis -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative

noncomputable section

/-! A second origin trivialization descends with the actual recovered
line whenever the quotient preserves the group origin. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme.{0}} {A B Q : Over S} [GrpObj A] [GrpObj B] [GrpObj Q]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]
  (D : RigidifiedLine.Construction.RelativeRigidifiedProductLine A B) (q : B ⟶ Q) [IsMonHom q]
  (H : ∀ {T : Over S} [IsLocallyNoetherian T.left] (a b : T ⟶ B),
    a ≫ q = b ≫ q → D.relativeValue a = D.relativeValue b)
  [IsAffineHom (q ⊗ₘ 𝟙 A).left] [Flat (q ⊗ₘ 𝟙 A).left]
  [Surjective (q ⊗ₘ 𝟙 A).left] [LocallyOfFinitePresentation (q ⊗ₘ 𝟙 A).left]
  [IsLocallyNoetherian (Q ⊗ A).left]
  (hz : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (lift (1 : A ⟶ B) (𝟙 A)).left
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.bundle) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass A.left)

include hz in
theorem RigidifiedLine.Construction.RelativeRigidifiedProductLine.normalizedQuotientLine_secondAxis_class :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (lift (1 : A ⟶ Q) (𝟙 A)).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.normalizedQuotientLine q H)) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass A.left := by
  have he : (lift (1 : A ⟶ B) (𝟙 A)).left ≫ (q ⊗ₘ 𝟙 A).left =
      (lift (1 : A ⟶ Q) (𝟙 A)).left :=
    congrArg Over.Hom.left (by simp : lift (1 : A ⟶ B) (𝟙 A) ≫ (q ⊗ₘ 𝟙 A) =
      lift (1 : A ⟶ Q) (𝟙 A))
  rw [← he, AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, D.normalizedQuotientLine_pullback_class q H]
  exact hz

def RigidifiedLine.Construction.RelativeRigidifiedProductLine.normalizedQuotientLine_secondAxis :
    (Scheme.Modules.pullback (lift (1 : A ⟶ Q) (𝟙 A)).left).obj
      (D.normalizedQuotientLine q H).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left :=
  Classical.choice (Quotient.exact (D.normalizedQuotientLine_secondAxis_class q H hz))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative
