import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Universal.Homogeneity
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Universal.SecondAxis
import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledDualData

/-! # Dual Data -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient

noncomputable section

/-! Full dual data from an actual Picard quotient: representation,
homogeneity, universal Poincare bundle, and both origin normalizations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard

variable {S : Scheme.{0}} {A B Q : Over S} [GrpObj A] [GrpObj B] [GrpObj Q]
  (D : Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine A B) (hΓ : GlobalFunctions.Construction.HasUniversalGlobalFunctions A) (q : B ⟶ Q) [IsMonHom q]
  (H : ∀ {T : Over S} (a b : T ⟶ B),
    a ≫ q = b ≫ q → D.relativeValue a = D.relativeValue b)
  [IsAffineHom (q ⊗ₘ 𝟙 A).left] [Flat (q ⊗ₘ 𝟙 A).left]
  [Surjective (q ⊗ₘ 𝟙 A).left]
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
def Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine.universalPicardQuotientDualData : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A where
  abelian := Q
  group := inferInstance
  commutative := inferInstance
  proper := inferInstance
  smooth := inferInstance
  connected := inferInstance
  representable :=
    (Functor.RepresentableBy.equivUliftYonedaIso (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf A).obj Q).symm (asIso i)
  origin := h1
  poincare := D.universalNormalizedQuotientLine hΓ q H
  poincareHomogeneous := D.universalNormalizedQuotientLine_homogeneous hΓ q H hD
  universalClass := D.universalNormalizedQuotientLine_native_universal_class hΓ q H hD i hi
  normalizedAtAbelianZero := ⟨D.universalNormalizedQuotientLine_axis hΓ q H⟩
  normalizedAtDualZero := ⟨D.universalNormalizedQuotientLine_secondAxis hΓ q H hz⟩

theorem Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine.universalPicardQuotientDualData_value (T : Over S) (x : T ⟶ Q) :
    (D.universalPicardQuotientDualData hΓ q H hD hz i hi h1).representable.homEquiv x =
      i.app (op T) (ULift.up x) := rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient
