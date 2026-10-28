import OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionDescent
import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-! # Second Descent -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.SecondDescent

noncomputable section

/-!
# The second canonical coordinate descent obtained from symmetry of the biextension line
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

variable {S : Scheme.{u}} {A B : Over S} (f : A ⟶ B)
  (L : Line.Bundles.LineBundle (A ⊗ A).left) (Q : Line.Bundles.LineBundle (B ⊗ A).left)
  (e : (Scheme.Modules.pullback (f ⊗ₘ 𝟙 A).left).obj Q.sheaf ≅ L.sheaf)
  (symmetry : (Scheme.Modules.pullback (β_ A A).hom.left).obj L.sheaf ≅ L.sheaf)

/-- The actual line on the second quotient product is the first quotient line with the factors exchanged. -/
def secondLine : Line.Bundles.LineBundle (A ⊗ B).left := Q.pullback (β_ A B).hom.left

/-- Naturality of exchange makes the two actual quotient squares commute. -/
theorem exchange_square : (𝟙 A ⊗ₘ f) ≫ (β_ A B).hom = (β_ A A).hom ≫ (f ⊗ₘ 𝟙 A) :=
  BraidedCategory.braiding_naturality (𝟙 A) f

/-- The symmetry of the original line supplies the second quotient pullback isomorphism. -/
def secondPullbackIso :
    (Scheme.Modules.pullback (𝟙 A ⊗ₘ f).left).obj (secondLine Q).sheaf ≅ L.sheaf :=
  (Scheme.Modules.pullbackComp (𝟙 A ⊗ₘ f).left (β_ A B).hom.left).app Q.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left (exchange_square f))).app Q.sheaf ≪≫
    (Scheme.Modules.pullbackComp (β_ A A).hom.left (f ⊗ₘ 𝟙 A).left).symm.app Q.sheaf ≪≫
    (Scheme.Modules.pullback (β_ A A).hom.left).mapIso e ≪≫ symmetry

/-- Canonical ordinary descent of the actual second quotient line. -/
def quotientDatum : (Geometric.KernelLinearization.overModulePullbacks S).DescentData (fun (_ : PUnit.{1}) => 𝟙 A ⊗ₘ f) :=
  Pseudofunctor.DescentData.ofObj (F := Geometric.KernelLinearization.overModulePullbacks S) (f := fun (_ : PUnit.{1}) => 𝟙 A ⊗ₘ f)
    (secondLine Q).sheaf

/-- The second-coordinate descent datum on the original line is constructed from symmetry. -/
def sourceDatum : (Geometric.KernelLinearization.overModulePullbacks S).DescentData (fun (_ : PUnit.{1}) => 𝟙 A ⊗ₘ f) :=
  Ordinary.DescentObjectIso.ofIso (Geometric.KernelLinearization.overModulePullbacks S) (𝟙 A ⊗ₘ f)
    (quotientDatum f Q) L.sheaf (secondPullbackIso f L Q e symmetry).symm

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.SecondDescent
