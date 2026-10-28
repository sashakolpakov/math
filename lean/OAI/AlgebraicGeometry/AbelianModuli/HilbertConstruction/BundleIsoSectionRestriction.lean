import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.BundleIsoSheaf
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.IsoBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.BaseChangeFunctor

/-! # Bundle Iso Section Restriction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BundleIsoSectionRestriction

noncomputable section

/-! Restriction of relative bundle isomorphisms to a section is natural in the test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X S : Scheme.{u}} (p : X ⟶ S) (x : S ⟶ X) (hx : x ≫ p = 𝟙 S)
variable (L M : Line.Bundles.LineBundle X)

def bundleIsoRestrictionToSection : Relative.BundleIsoSheaf.relativeBundleIsoPresheaf p L M ⟶
    Module.IsoPresheaf.moduleIsoPresheaf ((Scheme.Modules.pullback x).obj L.sheaf) ((Scheme.Modules.pullback x).obj M.sheaf) :=
  Functor.whiskerRight (NatTrans.op (Section.BaseChangeFunctor.familyBaseChangeSection p x hx)) (Module.IsoPresheaf.moduleIsoPresheaf L.sheaf M.sheaf) ≫
    (Module.IsoBaseChange.moduleIsoBaseChangeIso x L.sheaf M.sheaf).inv

theorem bundleIsoRestrictionToSection_app (T : Over S)
    (e : (Relative.BundleIsoSheaf.relativeBundleIsoPresheaf p L M).obj (.op T)) :
    (bundleIsoRestrictionToSection p x hx L M).app (.op T) e =
      (Module.IsoBaseChange.moduleIsoBaseChangeEquiv x L.sheaf M.sheaf T).symm
        (Module.IsoSlicePullback.moduleIsoPullbackAlong ((Section.BaseChangeFunctor.familyBaseChangeSection p x hx).app T) e) := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BundleIsoSectionRestriction
