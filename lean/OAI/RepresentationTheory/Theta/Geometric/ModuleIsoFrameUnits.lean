import OAI.RepresentationTheory.Theta.Geometric.FrameTransitionUnitCoherence
import OAI.RepresentationTheory.Theta.Geometric.FrameGlobalIsoRestriction

/-! # Module Iso Frame Units -/

namespace OAI.RepresentationTheory.Theta.Geometric.ModuleIsoFrameUnits

noncomputable section

/-! An actual line-sheaf isomorphism has regular unit coefficients in
native frames, with restriction and change-of-frame formulas. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem frameTransitionUnit_precompose {X : Scheme} {M N : X.Modules} (f : M ≅ N) (U : X.Opens)
    (e g : N.restrict U.ι ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.toScheme) :
    IntrinsicFrame.TransitionUnits.frameTransitionUnit M U ((Scheme.Modules.restrictFunctor U.ι).mapIso f ≪≫ e)
      ((Scheme.Modules.restrictFunctor U.ι).mapIso f ≪≫ g) = IntrinsicFrame.TransitionUnits.frameTransitionUnit N U e g := by
  symm
  apply FrameTransitionUnitCoherence.frameTransitionUnit_unique
  change (Scheme.Modules.restrictFunctor U.ι).map f.hom ≫ e.hom =
    ((Scheme.Modules.restrictFunctor U.ι).map f.hom ≫ g.hom) ≫ _
  rw [IntrinsicFrame.TransitionUnits.frameTransitionUnit_spec N U e g, Category.assoc]

def moduleIsoFrameUnit {X : Scheme} {M N : X.Modules} (f : M ≅ N) (U : X.Opens)
    (e : M.restrict U.ι ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.toScheme)
    (g : N.restrict U.ι ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.toScheme) : Γ(X, U)ˣ :=
  IntrinsicFrame.TransitionUnits.frameTransitionUnit M U ((Scheme.Modules.restrictFunctor U.ι).mapIso f ≪≫ g) e

theorem moduleIsoFrameUnit_restrict {X : Scheme} {M N : X.Modules} (f : M ≅ N)
    {U V : X.Opens} (h : V ≤ U)
    (e : M.restrict U.ι ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.toScheme)
    (g : N.restrict U.ι ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.toScheme) :
    PowerGaugeCover.restrictRegularUnit h (moduleIsoFrameUnit f U e g) =
      moduleIsoFrameUnit f V (AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization h e)
        (AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization h g) := by
  unfold moduleIsoFrameUnit
  rw [FrameTransitionUnitCoherence.frameTransitionUnit_restrict, FrameGlobalIsoRestriction.restrictOpenFrame_globalIso]

theorem moduleIsoFrameUnit_transition {X : Scheme} {M N : X.Modules} (f : M ≅ N) (U : X.Opens)
    (e e' : M.restrict U.ι ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.toScheme)
    (g g' : N.restrict U.ι ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.toScheme) :
    moduleIsoFrameUnit f U e g * IntrinsicFrame.TransitionUnits.frameTransitionUnit M U e e' =
      IntrinsicFrame.TransitionUnits.frameTransitionUnit N U g g' * moduleIsoFrameUnit f U e' g' := by
  unfold moduleIsoFrameUnit
  rw [FrameTransitionUnitCoherence.frameTransitionUnit_comp]
  have H := FrameTransitionUnitCoherence.frameTransitionUnit_comp M U
    ((Scheme.Modules.restrictFunctor U.ι).mapIso f ≪≫ g)
    ((Scheme.Modules.restrictFunctor U.ι).mapIso f ≪≫ g') e'
  rw [frameTransitionUnit_precompose] at H
  exact H.symm

end

end OAI.RepresentationTheory.Theta.Geometric.ModuleIsoFrameUnits
