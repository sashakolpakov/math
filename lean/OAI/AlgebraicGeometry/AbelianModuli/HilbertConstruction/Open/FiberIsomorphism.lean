import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.PowerBaseChange
import Mathlib.AlgebraicGeometry.Fiber

/-! # Fiber Isomorphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.FiberIsomorphism

noncomputable section

/-! Open base change identifies actual scheme fibers and their pulled-back line bundles. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
variable {S X Y P : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}

def baseChangeFiberMap (H : IsPullback a b f g) (y : Y) : b.fiber y ⟶ f.fiber (g y) :=
  pullback.map b (Y.fromSpecResidueField y) f (S.fromSpecResidueField (g y))
    a (Spec.map (g.residueFieldMap y)) g H.w.symm (by simp)

@[reassoc]
theorem baseChangeFiberMap_fiberι (H : IsPullback a b f g) (y : Y) :
    baseChangeFiberMap H y ≫ f.fiberι (g y) = b.fiberι y ≫ a := by
  exact pullback.lift_fst _ _ _

@[reassoc]
theorem baseChangeFiberMap_structure (H : IsPullback a b f g) (y : Y) :
    baseChangeFiberMap H y ≫ f.fiberToSpecResidueField (g y) =
      b.fiberToSpecResidueField y ≫ Spec.map (g.residueFieldMap y) := by
  exact pullback.lift_snd _ _ _

def openBaseChangeFiberIso [IsOpenImmersion g] (H : IsPullback a b f g) (y : Y) :
    b.fiber y ≅ f.fiber (g y) := by
  have h := isPullback_fiberToSpecResidueField_of_isPullback H y
  have : IsIso (baseChangeFiberMap H y) := h.isIso_fst_of_isIso
  exact asIso (baseChangeFiberMap H y)

def baseChangeFiberBundleIso (H : IsPullback a b f g) (L : Line.Bundles.LineBundle X) (y : Y) :
    ((L.pullback (f.fiberι (g y))).pullback (baseChangeFiberMap H y)).sheaf ≅
      ((L.pullback a).pullback (b.fiberι y)).sheaf :=
  (Scheme.Modules.pullbackComp (baseChangeFiberMap H y) (f.fiberι (g y))).app L.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (baseChangeFiberMap_fiberι H y)).app L.sheaf ≪≫
    ((Scheme.Modules.pullbackComp (b.fiberι y) a).app L.sheaf).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.FiberIsomorphism
