import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles

/-! # Restriction Frame Image -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RestrictionFrameImage

noncomputable section

/-! A frame on an open of an open subscheme transports to a frame on its actual image in the original scheme. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) (V : U.toScheme.Opens)

def restrictionFrameImage
    (frame : (Scheme.Modules.pullback V.ι).obj (M.restrict U.ι) ≅ Line.Bundles.structureModule V.toScheme) :
    (Scheme.Modules.pullback (U.ι ''ᵁ V).ι).obj M ≅ Line.Bundles.structureModule (U.ι ''ᵁ V).toScheme := by
  let e := U.ι.isoImage V
  let localFrame : (Scheme.Modules.pullback (V.ι ≫ U.ι)).obj M ≅ Line.Bundles.structureModule V.toScheme :=
    (Scheme.Modules.pullbackComp V.ι U.ι).symm.app M ≪≫
      (Scheme.Modules.pullback V.ι).mapIso ((Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app M) ≪≫
        frame
  exact (Scheme.Modules.pullbackCongr (U.ι.isoImage_inv_ι V).symm).app M ≪≫
    (Scheme.Modules.pullbackComp e.inv (V.ι ≫ U.ι)).symm.app M ≪≫
      (Scheme.Modules.pullback e.inv).mapIso localFrame ≪≫ Line.Bundles.structureModulePullbackIso e.inv

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RestrictionFrameImage
