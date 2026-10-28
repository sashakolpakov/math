import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles

/-! # Inverse Line Pullback -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.InverseLinePullback

noncomputable section

/-! An isomorphism with the pullback along a scheme isomorphism
also gives the inverse pullback comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles
universe u

def inverseLinePullbackIso {X Y : Scheme.{u}} (e : X ≅ Y) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y)
    (h : L.sheaf ≅ (M.pullback e.hom).sheaf) : M.sheaf ≅ (L.pullback e.inv).sheaf :=
  (Scheme.Modules.pullbackId Y).symm.app M.sheaf ≪≫
    (Scheme.Modules.pullbackCongr e.inv_hom_id.symm).app M.sheaf ≪≫
      (Scheme.Modules.pullbackComp e.inv e.hom).symm.app M.sheaf ≪≫
        (Scheme.Modules.pullback e.inv).mapIso h.symm

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.InverseLinePullback
