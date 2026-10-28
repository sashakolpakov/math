import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Cartesian Bundle -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CartesianBundle.Construction.CartesianBundleTriviality

noncomputable section

/-! Triviality on a canonical fiber also holds on every Cartesian model
of that fiber. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles

universe u

def iso {X Y S T : Scheme.{u}} (f : Y ⟶ X) (π : X ⟶ S) (ρ : Y ⟶ T) (g : T ⟶ S)
    (h : IsPullback f ρ π g) (M : X.Modules)
    (e : (Scheme.Modules.pullback (pullback.fst π g)).obj M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (pullback π g)) :
    (Scheme.Modules.pullback f).obj M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y :=
  (Scheme.Modules.pullbackCongr h.isoPullback_hom_fst.symm).app M ≪≫
    ((Scheme.Modules.pullbackComp h.isoPullback.hom (pullback.fst π g)).app M).symm ≪≫
    (Scheme.Modules.pullback h.isoPullback.hom).mapIso e ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso h.isoPullback.hom

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CartesianBundle.Construction.CartesianBundleTriviality
