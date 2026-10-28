import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.KernelPair
import OAI.AlgebraicGeometry.FormalGeometry.Completion.EffectiveLineDescent

/-! # Line -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative

noncomputable section

/-! Actual relative line-bundle descent along an affine fppf quotient,
using its Noetherian kernel pair and the full ordinary descent datum. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

variable {S : Scheme.{0}} {A B Q : Over S} [GrpObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom] (D : RigidifiedLine.Construction.RelativeRigidifiedProductLine A B) (q : B ⟶ Q)
  (H : ∀ {T : Over S} [IsLocallyNoetherian T.left] (a b : T ⟶ B), a ≫ q = b ≫ q →
    D.relativeValue a = D.relativeValue b)

variable [LocallyOfFinitePresentation (q ⊗ₘ 𝟙 A).left]
  [IsLocallyNoetherian (Q ⊗ A).left]

set_option backward.isDefEq.respectTransparency false in
def RigidifiedLine.Construction.RelativeRigidifiedProductLine.quotientOrdinaryDatum :
    Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => (q ⊗ₘ 𝟙 A).left) := by
  have : IsLocallyNoetherian (B ⊗ A).left :=
    LocallyOfFiniteType.isLocallyNoetherian (q ⊗ₘ 𝟙 A).left
  exact Picard.PoincareBundle.UnderlyingDescent.underlyingDatum Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks (fun (_ : PUnit.{1}) => q ⊗ₘ 𝟙 A)
    (D.quotientOverDatum q H)

variable [IsAffineHom (q ⊗ₘ 𝟙 A).left] [Flat (q ⊗ₘ 𝟙 A).left]
  [Surjective (q ⊗ₘ 𝟙 A).left]

set_option backward.isDefEq.respectTransparency false in
def RigidifiedLine.Construction.RelativeRigidifiedProductLine.quotientLine : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (Q ⊗ A).left where
  sheaf := (Picard.PoincareBundle.Ordinary.GlobalLineDescent.descendedLine (q ⊗ₘ 𝟙 A).left
    (D.quotientOrdinaryDatum q H) D.bundle.locallyTrivial).sheaf
  locallyTrivial := (Picard.PoincareBundle.Ordinary.GlobalLineDescent.descendedLine (q ⊗ₘ 𝟙 A).left
    (D.quotientOrdinaryDatum q H) D.bundle.locallyTrivial).isLine

set_option backward.isDefEq.respectTransparency false in
def RigidifiedLine.Construction.RelativeRigidifiedProductLine.quotientLinePullbackIso :
    (Scheme.Modules.pullback (q ⊗ₘ 𝟙 A).left).obj (D.quotientLine q H).sheaf ≅ D.bundle.sheaf :=
  Picard.PoincareBundle.Ordinary.GlobalLineDescent.descendedLinePullbackIso (q ⊗ₘ 𝟙 A).left
    (D.quotientOrdinaryDatum q H) D.bundle.locallyTrivial

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative
