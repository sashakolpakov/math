import OAI.AlgebraicGeometry.HilbertScheme.Presentations.FrameTransitionCocycles
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.BaseChange

/-! # Frame Transition Pullback -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.FrameTransitionPullback

noncomputable section

/-! Frame-transition functions pull back as their actual regular
functions along every scheme morphism, including field-valued points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.BaseChange

universe u
variable {X Y : Scheme.{u}} (a : X ⟶ Y) {M : Y.Modules}

def pullbackFrame (e : M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) :
    (Scheme.Modules.pullback a).obj M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X :=
  (Scheme.Modules.pullback a).mapIso e ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso a

theorem frameTransitionValue_pullback (e f : M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) :
    FrameTransitionCocycles.frameTransitionValue (pullbackFrame a e) (pullbackFrame a f) =
      a.appTop (FrameTransitionCocycles.frameTransitionValue e f) := by
  unfold FrameTransitionCocycles.frameTransitionValue
  have h : (pullbackFrame a e).inv ≫ (pullbackFrame a f).hom =
      (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso a).inv ≫ (Scheme.Modules.pullback a).map (e.inv ≫ f.hom) ≫
        (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso a).hom := by
    simp only [pullbackFrame, Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom,
      Functor.mapIso_inv, Functor.map_comp, Category.assoc]
  rw [h, AbelianModuli.HilbertConstruction.Scalar.BaseChange.structureModuleEndValue_baseChange]

theorem frameTransitionUnit_pullback (e f : M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) :
    FrameTransitionCocycles.frameTransitionUnit (pullbackFrame a e) (pullbackFrame a f) =
      Units.map a.appTop.hom.toMonoidHom (FrameTransitionCocycles.frameTransitionUnit e f) := by
  apply Units.ext
  change (FrameTransitionCocycles.frameTransitionValue_isUnit (pullbackFrame a e) (pullbackFrame a f)).unit.val =
    a.appTop (FrameTransitionCocycles.frameTransitionValue_isUnit e f).unit.val
  rw [(FrameTransitionCocycles.frameTransitionValue_isUnit (pullbackFrame a e) (pullbackFrame a f)).unit_spec,
    (FrameTransitionCocycles.frameTransitionValue_isUnit e f).unit_spec, frameTransitionValue_pullback]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.FrameTransitionPullback
