import OAI.RepresentationTheory.Theta.Geometric.IntrinsicFrame.TransitionUnits
import OAI.RepresentationTheory.Theta.Geometric.OpenFrameScalars

/-! # Frame Transition Unit Coherence -/

namespace OAI.RepresentationTheory.Theta.Geometric.FrameTransitionUnitCoherence

noncomputable section

/-! Uniqueness and restriction coherence for the actual regular units
comparing native line frames. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem frameTransitionUnit_unique {X : Scheme} (M : X.Modules) (U : X.Opens)
    (e g : M.restrict U.ι ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.toScheme) (r : Γ(X, U)ˣ)
    (h : e.hom = g.hom ≫ AlgebraicGeometry.SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection (U.topIso.inv (r : Γ(X, U)))) :
    r = IntrinsicFrame.TransitionUnits.frameTransitionUnit M U e g := by
  apply Units.ext
  have H := (cancel_epi g.hom).mp (h.symm.trans (IntrinsicFrame.TransitionUnits.frameTransitionUnit_spec M U e g))
  have Hv := congrArg (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue U.toScheme) H
  rw [NonvanishingScalarPullback.endValue_unitEndomorphism, NonvanishingScalarPullback.endValue_unitEndomorphism] at Hv
  have H' := congrArg U.topIso.hom Hv
  simpa only [Iso.inv_hom_id_apply] using H'

theorem frameTransitionUnit_restrict {X : Scheme} (M : X.Modules) {U V : X.Opens} (h : V ≤ U)
    (e g : M.restrict U.ι ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.toScheme) :
    PowerGaugeCover.restrictRegularUnit h (IntrinsicFrame.TransitionUnits.frameTransitionUnit M U e g) =
      IntrinsicFrame.TransitionUnits.frameTransitionUnit M V (AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization h e)
        (AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization h g) := by
  apply frameTransitionUnit_unique
  exact OpenFrameScalars.restrictOpenFrame_scalar M h e g _ (IntrinsicFrame.TransitionUnits.frameTransitionUnit_spec M U e g)

theorem frameTransitionUnit_comp {X : Scheme} (M : X.Modules) (U : X.Opens)
    (e g h : M.restrict U.ι ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.toScheme) :
    IntrinsicFrame.TransitionUnits.frameTransitionUnit M U e g * IntrinsicFrame.TransitionUnits.frameTransitionUnit M U g h = IntrinsicFrame.TransitionUnits.frameTransitionUnit M U e h := by
  apply frameTransitionUnit_unique
  calc
    e.hom = g.hom ≫ AlgebraicGeometry.SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection (U.topIso.inv (IntrinsicFrame.TransitionUnits.frameTransitionUnit M U e g : Γ(X, U))) :=
      IntrinsicFrame.TransitionUnits.frameTransitionUnit_spec M U e g
    _ = h.hom ≫ AlgebraicGeometry.SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection (U.topIso.inv (IntrinsicFrame.TransitionUnits.frameTransitionUnit M U g h : Γ(X, U))) ≫
        AlgebraicGeometry.SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection (U.topIso.inv (IntrinsicFrame.TransitionUnits.frameTransitionUnit M U e g : Γ(X, U))) := by
      rw [← Category.assoc, ← IntrinsicFrame.TransitionUnits.frameTransitionUnit_spec M U g h]
    _ = _ := by rw [AlgebraicGeometry.SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection_comp, ← map_mul, mul_comm]; rfl

end

end OAI.RepresentationTheory.Theta.Geometric.FrameTransitionUnitCoherence
