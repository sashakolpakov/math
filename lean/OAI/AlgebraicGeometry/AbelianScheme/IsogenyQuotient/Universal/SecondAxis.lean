import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Universal.Normalization

/-! # Second Axis -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient

noncomputable section

/-! A second origin trivialization descends with the actual recovered
line whenever the quotient preserves the group origin. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme.{0}} {A B Q : Over S} [GrpObj A] [GrpObj B] [GrpObj Q]
  (D : Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine A B) (hΓ : GlobalFunctions.Construction.HasUniversalGlobalFunctions A) (q : B ⟶ Q) [IsMonHom q]
  (H : ∀ {T : Over S} (a b : T ⟶ B),
    a ≫ q = b ≫ q → D.relativeValue a = D.relativeValue b)
  [IsAffineHom (q ⊗ₘ 𝟙 A).left] [Flat (q ⊗ₘ 𝟙 A).left]
  [Surjective (q ⊗ₘ 𝟙 A).left]
  (hz : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (lift (1 : A ⟶ B) (𝟙 A)).left
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.bundle) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass A.left)

include hz in
theorem Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine.universalNormalizedQuotientLine_secondAxis_class :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (lift (1 : A ⟶ Q) (𝟙 A)).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.universalNormalizedQuotientLine hΓ q H)) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass A.left := by
  have he : (lift (1 : A ⟶ B) (𝟙 A)).left ≫ (q ⊗ₘ 𝟙 A).left =
      (lift (1 : A ⟶ Q) (𝟙 A)).left :=
    congrArg Over.Hom.left (by simp : lift (1 : A ⟶ B) (𝟙 A) ≫ (q ⊗ₘ 𝟙 A) =
      lift (1 : A ⟶ Q) (𝟙 A))
  rw [← he, AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, D.universalNormalizedQuotientLine_pullback_class hΓ q H]
  exact hz

def Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine.universalNormalizedQuotientLine_secondAxis :
    (Scheme.Modules.pullback (lift (1 : A ⟶ Q) (𝟙 A)).left).obj
      (D.universalNormalizedQuotientLine hΓ q H).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left :=
  Classical.choice (Quotient.exact (D.universalNormalizedQuotientLine_secondAxis_class hΓ q H hz))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient
