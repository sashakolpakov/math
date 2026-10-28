import OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.DescentObjectIso
import OAI.AlgebraicGeometry.Picard.PoincareBundle.UnderlyingDescent

/-! # First Biextension Descent -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionDescent

noncomputable section

/-!
# Canonical first-coordinate Poincare descent data from the actual quotient factorization
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

variable {S : Scheme.{u}} {A B Z X : Over S}
  (P : Line.Bundles.LineBundle (Z ⊗ X).left)
  (f : A ⟶ B) (μ : A ⟶ Z) (α : B ⟶ Z) (hα : f ≫ α = μ)

/-- Canonical descent of the actual line defined on the quotient product. -/
def quotientDatum : (Geometric.KernelLinearization.overModulePullbacks S).DescentData (fun (_ : PUnit.{1}) => f ⊗ₘ 𝟙 X) :=
  Pseudofunctor.DescentData.ofObj (F := Geometric.KernelLinearization.overModulePullbacks S) (f := fun (_ : PUnit.{1}) => f ⊗ₘ 𝟙 X)
    (FirstBiextensionFactor.descendedLine P α).sheaf

/-- Transfer canonical quotient descent to the original Poincare-family line through its actual isomorphism. -/
def sourceDatum : (Geometric.KernelLinearization.overModulePullbacks S).DescentData (fun (_ : PUnit.{1}) => f ⊗ₘ 𝟙 X) :=
  Ordinary.DescentObjectIso.ofIso (Geometric.KernelLinearization.overModulePullbacks S) (f ⊗ₘ 𝟙 X)
    (quotientDatum P f α) (FirstBiextensionFactor.familyLine P μ).sheaf (FirstBiextensionFactor.pullbackIso P f μ α hα).symm

/-- The first-coordinate datum has the original actual line sheaf as its object. -/
theorem sourceDatum_obj : (sourceDatum P f μ α hα).obj PUnit.unit = (FirstBiextensionFactor.familyLine P μ).sheaf := rfl

/-- The same canonical datum is ordinary geometric descent data on all underlying test schemes. -/
def ordinaryDatum : Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => (f ⊗ₘ 𝟙 X).left) :=
  UnderlyingDescent.underlyingDatum Geometric.KernelLinearization.modulePullbacks (fun (_ : PUnit.{1}) => f ⊗ₘ 𝟙 X)
    (sourceDatum P f μ α hα)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionDescent
