import OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified.QuotientNaturality
import OAI.AlgebraicGeometry.FormalGeometry.Completion.EffectiveLineDescent

/-! # Quotient Descent -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified

noncomputable section

/-! Effective descent of a rigidified product family. Equality of the
actual fiber classes constructs every gluing map and the full cocycle. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

variable {K : Type u} [Field K] [IsAlgClosed K] {A B Q : Over (Spec (.of K))} [GrpObj A]
  [IsProper A.hom] [IsIntegral A.left] (D : ProductLine.Construction.RigidifiedProductLine A B) (q : B ⟶ Q)
  (H : ∀ {T : Over (Spec (.of K))} (a b : T ⟶ B), a ≫ q = b ≫ q →
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.line a) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.line b))

def ProductLine.Construction.RigidifiedProductLine.quotientOverDatum :
    (Picard.PoincareBundle.Geometric.KernelLinearization.overModulePullbacks (Spec (.of K))).DescentData (fun (_ : PUnit.{1}) => q ⊗ₘ 𝟙 A) where
  obj _ := D.bundle.sheaf
  hom _T _p _i _j x y hx hy := D.quotientTransport q H x y (hx.trans hy.symm)
  hom_self _T _p _i x _hx := D.quotientTransport_self q H x
  hom_comp _T _p _i _j _k x y z hx hy hz :=
    D.quotientTransport_comp q H x y z (hx.trans hy.symm) (hy.trans hz.symm)
  pullHom_hom _U _T t _p _p' _hp _i _j x y hx hy x' y' htx hty :=
    D.quotientTransport_pullback q H t x y (hx.trans hy.symm) x' y' htx hty _

def ProductLine.Construction.RigidifiedProductLine.quotientOrdinaryDatum :
    Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => (q ⊗ₘ 𝟙 A).left) :=
  Picard.PoincareBundle.UnderlyingDescent.underlyingDatum Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks (fun (_ : PUnit.{1}) => q ⊗ₘ 𝟙 A)
    (D.quotientOverDatum q H)

variable [IsAffineHom (q ⊗ₘ 𝟙 A).left] [Flat (q ⊗ₘ 𝟙 A).left]
  [Surjective (q ⊗ₘ 𝟙 A).left] [IsLocallyNoetherian (Q ⊗ A).left]

def ProductLine.Construction.RigidifiedProductLine.quotientLine : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (Q ⊗ A).left where
  sheaf := (Picard.PoincareBundle.Ordinary.GlobalLineDescent.descendedLine (q ⊗ₘ 𝟙 A).left
    (D.quotientOrdinaryDatum q H) D.bundle.locallyTrivial).sheaf
  locallyTrivial := (Picard.PoincareBundle.Ordinary.GlobalLineDescent.descendedLine (q ⊗ₘ 𝟙 A).left
    (D.quotientOrdinaryDatum q H) D.bundle.locallyTrivial).isLine

def ProductLine.Construction.RigidifiedProductLine.quotientLinePullbackIso :
    (Scheme.Modules.pullback (q ⊗ₘ 𝟙 A).left).obj (D.quotientLine q H).sheaf ≅ D.bundle.sheaf :=
  Picard.PoincareBundle.Ordinary.GlobalLineDescent.descendedLinePullbackIso (q ⊗ₘ 𝟙 A).left
    (D.quotientOrdinaryDatum q H) D.bundle.locallyTrivial

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified
