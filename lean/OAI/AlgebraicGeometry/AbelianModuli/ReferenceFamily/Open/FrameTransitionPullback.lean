import OAI.RepresentationTheory.Theta.Geometric.FrameTransitionUnitCoherence
import OAI.RepresentationTheory.Theta.Geometric.Pullback.Algebraic
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.FunctionsBaseChange

/-! # Frame Transition Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Open.FrameTransitionPullback

noncomputable section

/-! The units of actual open frames pull back through the original
structure-sheaf map, including along the nonflat reduction morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem nativeOpenFrameTransition_self {X : Scheme.{0}} (M : X.Modules) (U : X.Opens)
    (e : M.restrict U.ι ≅ HilbertConstruction.Line.Bundles.structureModule U.toScheme) : RepresentationTheory.Theta.Geometric.IntrinsicFrame.TransitionUnits.frameTransitionUnit M U e e = 1 := by
  apply Units.ext
  change U.topIso.hom (RepresentationTheory.Theta.Geometric.IntrinsicFrame.TransitionUnits.frameTransitionTopUnit e e).val = 1
  rw [RepresentationTheory.Theta.Geometric.IntrinsicFrame.TransitionUnits.frameTransitionTopUnit_value, e.inv_hom_id]
  change U.topIso.hom (HilbertConstruction.Frame.Coordinates.structureModuleEndValue U.toScheme 1) = 1
  rw [map_one, map_one]

theorem nativeOpenFrameTransition_pullback {X Y : Scheme.{0}} (r : X ⟶ Y) (M : Y.Modules)
    (U : Y.Opens) (e f : M.restrict U.ι ≅ HilbertConstruction.Line.Bundles.structureModule U.toScheme) :
    Units.map (r.app U).hom.toMonoidHom (RepresentationTheory.Theta.Geometric.IntrinsicFrame.TransitionUnits.frameTransitionUnit M U e f) =
      RepresentationTheory.Theta.Geometric.IntrinsicFrame.TransitionUnits.frameTransitionUnit ((Scheme.Modules.pullback r).obj M) (r ⁻¹ᵁ U)
        (RepresentationTheory.Theta.Geometric.Pullback.Algebraic.pullbackOpenFrame r M U e) (RepresentationTheory.Theta.Geometric.Pullback.Algebraic.pullbackOpenFrame r M U f) := by
  apply RepresentationTheory.Theta.Geometric.FrameTransitionUnitCoherence.frameTransitionUnit_unique
  have h := ConcreteCategory.congr_hom (HilbertConstruction.Open.FunctionsBaseChange.morphismRestrict_appTop_topIso r U)
    (U.topIso.inv (RepresentationTheory.Theta.Geometric.IntrinsicFrame.TransitionUnits.frameTransitionUnit M U e f).val)
  change (r ⁻¹ᵁ U).topIso.hom ((r ∣_ U).appTop
    (U.topIso.inv (RepresentationTheory.Theta.Geometric.IntrinsicFrame.TransitionUnits.frameTransitionUnit M U e f).val)) =
      r.app U (U.topIso.hom (U.topIso.inv (RepresentationTheory.Theta.Geometric.IntrinsicFrame.TransitionUnits.frameTransitionUnit M U e f).val)) at h
  have hv : (r ∣_ U).appTop (U.topIso.inv (RepresentationTheory.Theta.Geometric.IntrinsicFrame.TransitionUnits.frameTransitionUnit M U e f).val) =
      (r ⁻¹ᵁ U).topIso.inv (r.app U (RepresentationTheory.Theta.Geometric.IntrinsicFrame.TransitionUnits.frameTransitionUnit M U e f).val) := by
    have hh := congrArg (fun s => (r ⁻¹ᵁ U).topIso.inv s) h
    exact (Iso.hom_inv_id_apply (r ⁻¹ᵁ U).topIso _).symm.trans
      (hh.trans (congrArg (fun s => (r ⁻¹ᵁ U).topIso.inv (r.app U s))
        (Iso.inv_hom_id_apply U.topIso _)))
  have he := RepresentationTheory.Theta.Geometric.Pullback.Algebraic.pullbackOpenFrame_scalar r M U e f _ (RepresentationTheory.Theta.Geometric.IntrinsicFrame.TransitionUnits.frameTransitionUnit_spec M U e f)
  rw [hv] at he
  exact he

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Open.FrameTransitionPullback
