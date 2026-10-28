import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles

/-! # Line Frame Pullback Square -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.LineFramePullbackSquare.Construction

noncomputable section

/-! An actual pullback frame is transported through a commuting
square by the canonical sheaf pullback composition isomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles

universe u

def lineFramePullbackSquare {X Y : Scheme.{u}} (f : X ⟶ X) (g : Y ⟶ Y) (h : Y ⟶ X)
    (hs : g ≫ h = h ≫ f) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ (L.pullback f).sheaf) :
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ≅ ((L.pullback h).pullback g).sheaf :=
  (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso h).symm ≪≫ (Scheme.Modules.pullback h).mapIso s ≪≫
    (Scheme.Modules.pullbackComp h f).app L.sheaf ≪≫
      (Scheme.Modules.pullbackCongr hs.symm).app L.sheaf ≪≫ ((Scheme.Modules.pullbackComp g h).app L.sheaf).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.LineFramePullbackSquare.Construction
