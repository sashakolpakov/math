import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.Naturality
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.KernelPair
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RestrictedKernelPairDescent

/-! # Kernel Pair -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative

noncomputable section

/-! Canonical normalized comparisons on the Noetherian kernel pair
give descent data on all test schemes. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RestrictedKernelPairDescent.Construction.KernelPairDescent

variable {S : Scheme.{0}} {A B Q : Over S} [GrpObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]
  (D : RigidifiedLine.Construction.RelativeRigidifiedProductLine A B) (q : B ⟶ Q)
  (H : ∀ {T : Over S} [IsLocallyNoetherian T.left] (a b : T ⟶ B),
    a ≫ q = b ≫ q → D.relativeValue a = D.relativeValue b)

set_option backward.isDefEq.respectTransparency false in
def RigidifiedLine.Construction.RelativeRigidifiedProductLine.quotientRestrictedTransport {T : Over S} (hT : IsLocallyNoetherian T.left)
    (x y : T ⟶ B ⊗ A) (h : x ≫ (q ⊗ₘ 𝟙 A) = y ≫ (q ⊗ₘ 𝟙 A)) :
    Kernel.PairDescent.Construction.KernelPairDescent.pointObject (X := B ⊗ A) (Picard.PoincareBundle.Geometric.KernelLinearization.overModulePullbacks S) D.bundle.sheaf x ⟶
      Kernel.PairDescent.Construction.KernelPairDescent.pointObject (X := B ⊗ A) (Picard.PoincareBundle.Geometric.KernelLinearization.overModulePullbacks S) D.bundle.sheaf y := by
  let := hT
  exact D.quotientTransport q H x y h

set_option backward.isDefEq.respectTransparency false in
theorem RigidifiedLine.Construction.RelativeRigidifiedProductLine.quotientRestrictedTransport_self {T : Over S} (hT : IsLocallyNoetherian T.left)
    (x : T ⟶ B ⊗ A) : D.quotientRestrictedTransport q H hT x x rfl = 𝟙 _ := by
  let := hT
  exact D.quotientTransport_self q H x

set_option backward.isDefEq.respectTransparency false in
theorem RigidifiedLine.Construction.RelativeRigidifiedProductLine.quotientRestrictedTransport_comp {T : Over S} (hT : IsLocallyNoetherian T.left)
    (x y z : T ⟶ B ⊗ A) (hxy : x ≫ (q ⊗ₘ 𝟙 A) = y ≫ (q ⊗ₘ 𝟙 A))
    (hyz : y ≫ (q ⊗ₘ 𝟙 A) = z ≫ (q ⊗ₘ 𝟙 A)) :
    D.quotientRestrictedTransport q H hT x y hxy ≫ D.quotientRestrictedTransport q H hT y z hyz =
      D.quotientRestrictedTransport q H hT x z (hxy.trans hyz) := by
  let := hT
  exact D.quotientTransport_comp q H x y z hxy hyz

set_option backward.isDefEq.respectTransparency false in
theorem RigidifiedLine.Construction.RelativeRigidifiedProductLine.quotientRestrictedTransport_pullback {T U : Over S}
    (hT : IsLocallyNoetherian T.left) (hU : IsLocallyNoetherian U.left) (t : U ⟶ T)
    (x y : T ⟶ B ⊗ A) (h : x ≫ (q ⊗ₘ 𝟙 A) = y ≫ (q ⊗ₘ 𝟙 A))
    (x' y' : U ⟶ B ⊗ A) (hx : t ≫ x = x') (hy : t ≫ y = y')
    (h' : x' ≫ (q ⊗ₘ 𝟙 A) = y' ≫ (q ⊗ₘ 𝟙 A)) :
    CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom
      (F := Picard.PoincareBundle.Geometric.KernelLinearization.overModulePullbacks S) (X₁ := B ⊗ A) (X₂ := B ⊗ A)
      (M₁ := D.bundle.sheaf) (M₂ := D.bundle.sheaf)
      (D.quotientRestrictedTransport q H hT x y h) t x' y' hx hy =
        D.quotientRestrictedTransport q H hU x' y' h' := by
  let := hT
  let := hU
  exact D.quotientTransport_pullback q H t x y h x' y' hx hy h'

variable [IsLocallyNoetherian (B ⊗ A).left] [LocallyOfFinitePresentation (q ⊗ₘ 𝟙 A).left]

def RigidifiedLine.Construction.RelativeRigidifiedProductLine.quotientKernelPairDatum : Kernel.PairDescent.Construction.KernelPairDescent.Datum (q ⊗ₘ 𝟙 A) (Picard.PoincareBundle.Geometric.KernelLinearization.overModulePullbacks S) D.bundle.sheaf :=
  RestrictedKernelPairDescent.Construction.KernelPairDescent.ofRestrictedTransport (q ⊗ₘ 𝟙 A) (Picard.PoincareBundle.Geometric.KernelLinearization.overModulePullbacks S) D.bundle.sheaf
    (fun T : Over S => IsLocallyNoetherian T.left)
    (D.quotientRestrictedTransport q H) (D.quotientRestrictedTransport_self q H)
    (D.quotientRestrictedTransport_comp q H) (D.quotientRestrictedTransport_pullback q H)
    inferInstance (Noetherian.KernelPair.Construction.kernelPair_noetherian (q ⊗ₘ 𝟙 A)) (Noetherian.KernelPair.Construction.kernelPair_triple_noetherian (q ⊗ₘ 𝟙 A))

def RigidifiedLine.Construction.RelativeRigidifiedProductLine.quotientOverDatum :
    (Picard.PoincareBundle.Geometric.KernelLinearization.overModulePullbacks S).DescentData (fun (_ : PUnit.{1}) => q ⊗ₘ 𝟙 A) :=
  Kernel.PairDescent.Construction.KernelPairDescent.toDescentData (q ⊗ₘ 𝟙 A) (Picard.PoincareBundle.Geometric.KernelLinearization.overModulePullbacks S) D.bundle.sheaf (D.quotientKernelPairDatum q H)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative
