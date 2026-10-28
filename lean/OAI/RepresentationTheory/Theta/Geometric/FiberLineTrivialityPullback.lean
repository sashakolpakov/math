import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles
import Mathlib.AlgebraicGeometry.Fiber

/-! # Fiber Line Triviality Pullback -/

namespace OAI.RepresentationTheory.Theta.Geometric.FiberLineTrivialityPullback

noncomputable section

/-! Triviality of a line bundle on a scheme-theoretic fiber pulls back
through the actual square, including the residue-field comparison. -/

set_option backward.isDefEq.respectTransparency false
open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles

universe u

def fiberSquareMap {X Y S T : Scheme.{u}} (f : Y ⟶ X) (ρ : Y ⟶ T)
    (π : X ⟶ S) (g : T ⟶ S) (h : f ≫ π = ρ ≫ g) (y : T) :
    ρ.fiber y ⟶ π.fiber (g y) :=
  pullback.map _ _ _ _ f (Spec.map (g.residueFieldMap y)) g h.symm
    (g.SpecMap_residueFieldMap_fromSpecResidueField y).symm

theorem fiberSquareMap_fst {X Y S T : Scheme.{u}} (f : Y ⟶ X) (ρ : Y ⟶ T)
    (π : X ⟶ S) (g : T ⟶ S) (h : f ≫ π = ρ ≫ g) (y : T) :
    fiberSquareMap f ρ π g h y ≫ π.fiberι (g y) = ρ.fiberι y ≫ f := by
  simp only [fiberSquareMap, pullback.map, Scheme.Hom.fiberι, pullback.lift_fst]

def fiberTrivializationPullback {X Y S T : Scheme.{u}} (f : Y ⟶ X) (ρ : Y ⟶ T)
    (π : X ⟶ S) (g : T ⟶ S) (h : f ≫ π = ρ ≫ g) (y : T) (M : X.Modules)
    (e : (Scheme.Modules.pullback (π.fiberι (g y))).obj M ≅ OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (π.fiber (g y))) :
    (Scheme.Modules.pullback (ρ.fiberι y)).obj ((Scheme.Modules.pullback f).obj M) ≅
      OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (ρ.fiber y) :=
  (Scheme.Modules.pullbackComp (ρ.fiberι y) f).app M ≪≫
    (Scheme.Modules.pullbackCongr (fiberSquareMap_fst f ρ π g h y).symm).app M ≪≫
    ((Scheme.Modules.pullbackComp (fiberSquareMap f ρ π g h y) (π.fiberι (g y))).app M).symm ≪≫
    (Scheme.Modules.pullback (fiberSquareMap f ρ π g h y)).mapIso e ≪≫
    OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (fiberSquareMap f ρ π g h y)

end

end OAI.RepresentationTheory.Theta.Geometric.FiberLineTrivialityPullback
