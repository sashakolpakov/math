import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.LineValue
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.HomogeneousPicardDescent
import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledPoincareDetection

/-! # Homogeneity -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative

noncomputable section

/-! The actual normalized quotient line remains homogeneous and its
native homogeneous Picard class is the prescribed representing section. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledPoincareDetection.Construction.UnbundledPicard

variable {S : Scheme.{0}} {A B Q : Over S} [GrpObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]
  (D : RigidifiedLine.Construction.RelativeRigidifiedProductLine A B) (q : B ⟶ Q)
  (H : ∀ {T : Over S} [IsLocallyNoetherian T.left] (a b : T ⟶ B),
    a ≫ q = b ≫ q → D.relativeValue a = D.relativeValue b)
  [IsAffineHom (q ⊗ₘ 𝟙 A).left] [Flat (q ⊗ₘ 𝟙 A).left]
  [Surjective (q ⊗ₘ 𝟙 A).left] [LocallyOfFinitePresentation (q ⊗ₘ 𝟙 A).left]
  [IsLocallyNoetherian (Q ⊗ A).left]
  [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left]
  (hD : Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.IsHomogeneousPicardClass A B (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.bundle))

include hD in
set_option backward.isDefEq.respectTransparency false in
theorem RigidifiedLine.Construction.RelativeRigidifiedProductLine.normalizedQuotientLine_homogeneous :
    Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.IsHomogeneousPicardClass A Q (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.normalizedQuotientLine q H)) := by
  apply HomogeneousPicardDescent.Construction.homogeneousPicardClass_of_fppf_pullback A q
  change Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.IsHomogeneousPicardClass A B (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (q ⊗ₘ 𝟙 A).left
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.normalizedQuotientLine q H)))
  rw [D.normalizedQuotientLine_pullback_class q H]
  exact hD

variable (i : uliftYoneda.{1}.obj Q ⟶ (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf A).obj)
  (hi : ∀ (T : Over S) (a : T ⟶ B), D.relativeValue a =
    (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheafInclusion A).hom.app (op T) (i.app (op T) (ULift.up (a ≫ q))))

include hi in
set_option backward.isDefEq.respectTransparency false in
theorem RigidifiedLine.Construction.RelativeRigidifiedProductLine.normalizedQuotientLine_native_universal_class :
    i.app (op Q) (ULift.up (𝟙 Q)) =
      (toSheafify (Scheme.fppfTopology.over S) (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf A)).app (op Q)
        ⟨AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.normalizedQuotientLine q H),
          D.normalizedQuotientLine_homogeneous q H hD⟩ := by
  have : Mono ((Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheafInclusion A).hom.app (op Q)) := inferInstance
  apply (CategoryTheory.mono_iff_injective _).mp this
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app
    (Picard.Homomorphisms.UnbundledPoincareDetection.Construction.UnbundledPicard.homogeneousPicardSheafInclusion_toSheafify A) (op Q))
    (show (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf A).obj (op Q) from
      ⟨AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.normalizedQuotientLine q H), D.normalizedQuotientLine_homogeneous q H hD⟩)
  exact (D.normalizedQuotientLine_universal_class q H
    (i ≫ (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheafInclusion A).hom) hi).symm.trans h.symm

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative
