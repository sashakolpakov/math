import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles

/-! # Square Frame -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.LineBundle.SquareFrame

noncomputable section

/-! A line-bundle frame pulls back through an actual commutative
section square, using the native module pullback comparisons. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def lineBundleSquareFrame {X Y B C : Scheme.{0}} (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    (z : B ⟶ X) (frame : (L.pullback z).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule B)
    (s : Y ⟶ X) (z' : C ⟶ Y) (r : C ⟶ B) (w : z' ≫ s = r ≫ z) :
    ((L.pullback s).pullback z').sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule C :=
  (Scheme.Modules.pullbackComp z' s).app L.sheaf ≪≫
    (Scheme.Modules.pullbackCongr w).app L.sheaf ≪≫
    (Scheme.Modules.pullbackComp r z).symm.app L.sheaf ≪≫
    (Scheme.Modules.pullback r).mapIso frame ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso r

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.LineBundle.SquareFrame
