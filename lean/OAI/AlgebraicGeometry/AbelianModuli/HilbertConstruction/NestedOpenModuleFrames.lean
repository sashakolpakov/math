import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles

/-! # Nested Open Module Frames -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NestedOpenModuleFrames

noncomputable section

/-! Restriction of an actual structure-module frame to a smaller open. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

def nestedRestrictionIso {X : Scheme.{u}} {U V : X.Opens} (h : V ≤ U)
    (M : X.Modules) : M.restrict V.ι ≅
      (M.restrict U.ι).restrict (X.homOfLE h) :=
  (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι h).symm).app M ≪≫
    (Scheme.Modules.restrictFunctorComp (X.homOfLE h) U.ι).app M

def nativeOpenFrame {X : Scheme.{u}} {M : X.Modules} {U V : X.Opens}
    (h : V ≤ U) (e : M.restrict U.ι ≅ Line.Bundles.structureModule U.toScheme) :
    M.restrict V.ι ≅ Line.Bundles.structureModule V.toScheme :=
  nestedRestrictionIso h M ≪≫
    (Scheme.Modules.restrictFunctor (X.homOfLE h)).mapIso e ≪≫
    Scheme.Modules.restrictUnitIso (X.homOfLE h)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NestedOpenModuleFrames
