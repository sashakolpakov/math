import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle
import Mathlib.AlgebraicGeometry.Fiber

/-! # Fiber Triviality Base Change -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FiberTrivialityBaseChange.Construction

noncomputable section

/-! A fiber trivialization pulls back along any commuting square of schemes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

def pullbackTrivialization_comp
    {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y) (L : X.Modules)
    (e : (Scheme.Modules.pullback f).obj L ≅ LineBundle.Construction.structureSheafModule Y) :
    (Scheme.Modules.pullback (g ≫ f)).obj L ≅ LineBundle.Construction.structureSheafModule Z :=
  ((Scheme.Modules.pullbackComp g f).app L).symm ≪≫
    (Scheme.Modules.pullback g).mapIso e ≪≫ LineBundle.Construction.pullbackStructureSheafIso g

def lineBundleFiberMap
    {X Y S T : Scheme.{u}} (f : Y ⟶ X) (π : X ⟶ S) (ρ : Y ⟶ T) (g : T ⟶ S)
    (h : f ≫ π = ρ ≫ g) (t : T) : ρ.fiber t ⟶ π.fiber (g t) :=
  pullback.lift (ρ.fiberι t ≫ f)
    (ρ.fiberToSpecResidueField t ≫ Spec.map (g.residueFieldMap t)) (by
      rw [Category.assoc, h, ← Category.assoc, ρ.fiber_fac,
        Category.assoc, Category.assoc, g.SpecMap_residueFieldMap_fromSpecResidueField])

theorem lineBundleFiberMap_ι
    {X Y S T : Scheme.{u}} (f : Y ⟶ X) (π : X ⟶ S) (ρ : Y ⟶ T) (g : T ⟶ S)
    (h : f ≫ π = ρ ≫ g) (t : T) :
    lineBundleFiberMap f π ρ g h t ≫ π.fiberι (g t) = ρ.fiberι t ≫ f :=
  pullback.lift_fst _ _ _

def lineBundleFiberTrivialization_baseChange
    {X Y S T : Scheme.{u}} (f : Y ⟶ X) (π : X ⟶ S) (ρ : Y ⟶ T) (g : T ⟶ S)
    (h : f ≫ π = ρ ≫ g) (L : X.Modules) (t : T)
    (e : (Scheme.Modules.pullback (π.fiberι (g t))).obj L ≅ LineBundle.Construction.structureSheafModule (π.fiber (g t))) :
    (Scheme.Modules.pullback (ρ.fiberι t)).obj ((Scheme.Modules.pullback f).obj L) ≅
      LineBundle.Construction.structureSheafModule (ρ.fiber t) :=
  (Scheme.Modules.pullbackComp (ρ.fiberι t) f).app L ≪≫
    (Scheme.Modules.pullbackCongr (lineBundleFiberMap_ι f π ρ g h t).symm).app L ≪≫
    pullbackTrivialization_comp (π.fiberι (g t)) (lineBundleFiberMap f π ρ g h t) L e

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FiberTrivialityBaseChange.Construction
