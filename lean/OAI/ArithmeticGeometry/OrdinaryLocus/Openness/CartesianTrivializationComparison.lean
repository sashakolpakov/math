import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FiberTrivialityBaseChange
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CartesianBundle

/-! # Cartesian Trivialization Comparison -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.CartesianTrivializationComparison.Construction

noncomputable section

/-! Transfer an actual line-bundle trivialization between two Cartesian models. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

def cartesianTrivialization_to_native
    {X Y S T : Scheme.{u}} (f : Y ⟶ X) (π : X ⟶ S) (ρ : Y ⟶ T) (g : T ⟶ S)
    (hp : IsPullback f ρ π g) (L : X.Modules)
    (e : (Scheme.Modules.pullback f).obj L ≅ LineBundle.Construction.structureSheafModule Y) :
    (Scheme.Modules.pullback (pullback.fst π g)).obj L ≅ LineBundle.Construction.structureSheafModule (pullback π g) :=
  (Scheme.Modules.pullbackCongr hp.isoPullback_inv_fst.symm).app L ≪≫
    FiberTrivialityBaseChange.Construction.pullbackTrivialization_comp f hp.isoPullback.inv L e

def cartesianTrivialization_transfer
    {X Y Z S T : Scheme.{u}} (f : Y ⟶ X) (f' : Z ⟶ X) (π : X ⟶ S)
    (ρ : Y ⟶ T) (ρ' : Z ⟶ T) (g : T ⟶ S)
    (hp : IsPullback f ρ π g) (hp' : IsPullback f' ρ' π g) (L : X.Modules)
    (e : (Scheme.Modules.pullback f).obj L ≅ LineBundle.Construction.structureSheafModule Y) :
    (Scheme.Modules.pullback f').obj L ≅ LineBundle.Construction.structureSheafModule Z :=
  AlgebraicGeometry.Quotients.FiniteDescent.CartesianBundle.Construction.CartesianBundleTriviality.iso f' π ρ' g hp' L
    (cartesianTrivialization_to_native f π ρ g hp L e)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.CartesianTrivializationComparison.Construction
