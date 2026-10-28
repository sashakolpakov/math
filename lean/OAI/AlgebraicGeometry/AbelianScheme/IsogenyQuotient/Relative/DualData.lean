import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.Homogeneity
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.SecondAxis
import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledDualData

/-! # Dual Data -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative

noncomputable section

/-! Full dual data from an actual Picard quotient: representation,
homogeneity, universal Poincare bundle, and both origin normalizations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard

variable {S : Scheme.{0}} {A B Q : Over S} [GrpObj A] [GrpObj B] [GrpObj Q]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]
  (D : RigidifiedLine.Construction.RelativeRigidifiedProductLine A B) (q : B ⟶ Q) [IsMonHom q]
  (H : ∀ {T : Over S} [IsLocallyNoetherian T.left] (a b : T ⟶ B),
    a ≫ q = b ≫ q → D.relativeValue a = D.relativeValue b)
  [IsAffineHom (q ⊗ₘ 𝟙 A).left] [Flat (q ⊗ₘ 𝟙 A).left]
  [Surjective (q ⊗ₘ 𝟙 A).left] [LocallyOfFinitePresentation (q ⊗ₘ 𝟙 A).left]
  [IsLocallyNoetherian (Q ⊗ A).left]
  [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left]
  (hD : Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.IsHomogeneousPicardClass A B (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.bundle))
  (hz : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (lift (1 : A ⟶ B) (𝟙 A)).left
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.bundle) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass A.left)
  (i : uliftYoneda.{1}.obj Q ⟶ (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf A).obj)
  (hi : ∀ (T : Over S) (a : T ⟶ B), D.relativeValue a =
    (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheafInclusion A).hom.app (op T) (i.app (op T) (ULift.up (a ≫ q))))
  (h1 : ∀ T : Over S, i.app (op T) (ULift.up (1 : T ⟶ Q)) = Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.trivialHomogeneousPicardClass A T)
  [IsCommMonObj Q] [IsProper Q.hom] [Smooth Q.hom] [GeometricallyConnected Q.hom] [IsIso i]

set_option backward.isDefEq.respectTransparency false in
def RigidifiedLine.Construction.RelativeRigidifiedProductLine.relativePicardQuotientDualData : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A where
  abelian := Q
  group := inferInstance
  commutative := inferInstance
  proper := inferInstance
  smooth := inferInstance
  connected := inferInstance
  representable :=
    (Functor.RepresentableBy.equivUliftYonedaIso (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf A).obj Q).symm (asIso i)
  origin := h1
  poincare := D.normalizedQuotientLine q H
  poincareHomogeneous := D.normalizedQuotientLine_homogeneous q H hD
  universalClass := D.normalizedQuotientLine_native_universal_class q H hD i hi
  normalizedAtAbelianZero := ⟨D.normalizedQuotientLine_axis q H⟩
  normalizedAtDualZero := ⟨D.normalizedQuotientLine_secondAxis q H hz⟩

theorem RigidifiedLine.Construction.RelativeRigidifiedProductLine.relativePicardQuotientDualData_value (T : Over S) (x : T ⟶ Q) :
    (D.relativePicardQuotientDualData q H hD hz i hi h1).representable.homEquiv x =
      i.app (op T) (ULift.up x) := rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative
