import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Universal.Naturality
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ArbitraryGlobalLineDescent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.UnderlyingDescent

/-! # Line -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient

noncomputable section

/-! Universal normalized comparisons construct an ordinary descent
datum and an actual quotient line over arbitrary parameter schemes. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

variable {S : Scheme.{0}} {A B Q : Over S} [GrpObj A]
  (D : Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine A B) (hΓ : GlobalFunctions.Construction.HasUniversalGlobalFunctions A) (q : B ⟶ Q)
  (H : ∀ {T : Over S} (a b : T ⟶ B), a ≫ q = b ≫ q → D.relativeValue a = D.relativeValue b)

def Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine.universalQuotientOverDatum :
    (Picard.PoincareBundle.Geometric.KernelLinearization.overModulePullbacks S).DescentData (fun (_ : PUnit.{1}) => q ⊗ₘ 𝟙 A) where
  obj _ := D.bundle.sheaf
  hom _T _p _i _j x y hx hy := D.universalQuotientTransport hΓ q H x y (hx.trans hy.symm)
  hom_self _T _p _i x _hx := D.universalQuotientTransport_self hΓ q H x
  hom_comp _T _p _i _j _k x y z hx hy hz :=
    D.universalQuotientTransport_comp hΓ q H x y z (hx.trans hy.symm) (hy.trans hz.symm)
  pullHom_hom _U _T t _p _p' _hp _i _j x y hx hy x' y' htx hty :=
    D.universalQuotientTransport_pullback hΓ q H t x y (hx.trans hy.symm) x' y' htx hty _

set_option backward.isDefEq.respectTransparency false in
def Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine.universalQuotientOrdinaryDatum :
    Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => (q ⊗ₘ 𝟙 A).left) :=
  Picard.PoincareBundle.UnderlyingDescent.underlyingDatum Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks (fun (_ : PUnit.{1}) => q ⊗ₘ 𝟙 A)
    (D.universalQuotientOverDatum hΓ q H)

variable [IsAffineHom (q ⊗ₘ 𝟙 A).left] [Flat (q ⊗ₘ 𝟙 A).left] [Surjective (q ⊗ₘ 𝟙 A).left]

set_option backward.isDefEq.respectTransparency false in
def Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine.universalQuotientLine : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (Q ⊗ A).left where
  sheaf := (ArbitraryGlobalLineDescent.Construction.arbitraryDescendedLine (q ⊗ₘ 𝟙 A).left
    (D.universalQuotientOrdinaryDatum hΓ q H) D.bundle.locallyTrivial).sheaf
  locallyTrivial := (ArbitraryGlobalLineDescent.Construction.arbitraryDescendedLine (q ⊗ₘ 𝟙 A).left
    (D.universalQuotientOrdinaryDatum hΓ q H) D.bundle.locallyTrivial).isLine

set_option backward.isDefEq.respectTransparency false in
def Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine.universalQuotientLinePullbackIso :
    (Scheme.Modules.pullback (q ⊗ₘ 𝟙 A).left).obj (D.universalQuotientLine hΓ q H).sheaf ≅ D.bundle.sheaf :=
  ArbitraryGlobalLineDescent.Construction.arbitraryDescendedLinePullbackIso (q ⊗ₘ 𝟙 A).left
    (D.universalQuotientOrdinaryDatum hΓ q H) D.bundle.locallyTrivial

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient
