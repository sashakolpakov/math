import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.TwistOverFrames
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OpenRestrictionComposition

/-! # Frame Global Iso Restriction -/

namespace OAI.RepresentationTheory.Theta.Geometric.FrameGlobalIsoRestriction

noncomputable section

/-! Restriction of native frames respects a global sheaf isomorphism. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.SheafCohomology.Projective.OpenRestrictionComposition
universe u

theorem restrictOpenFrame_globalIso {X : Scheme.{u}} {M N : X.Modules} (a : M ≅ N)
    {U V : X.Opens} (h : V ≤ U)
    (e : N.restrict U.ι ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj U.toScheme) :
    AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization h ((Scheme.Modules.restrictFunctor U.ι).mapIso a ≪≫ e) =
      (Scheme.Modules.restrictFunctor V.ι).mapIso a ≪≫ AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization h e := by
  rw [← AlgebraicGeometry.SheafCohomology.Projective.OpenRestrictionComposition.nativeOpenFrame_eq_over, ← AlgebraicGeometry.SheafCohomology.Projective.OpenRestrictionComposition.nativeOpenFrame_eq_over]
  let α := Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι h).symm ≪≫
    Scheme.Modules.restrictFunctorComp (X.homOfLE h) U.ι
  have hn := α.hom.naturality a.hom
  change (Scheme.Modules.restrictFunctor V.ι).map a.hom ≫ (AlgebraicGeometry.SheafCohomology.Projective.OpenRestrictionComposition.nestedRestrictionIso h N).hom =
    (AlgebraicGeometry.SheafCohomology.Projective.OpenRestrictionComposition.nestedRestrictionIso h M).hom ≫
      (Scheme.Modules.restrictFunctor (X.homOfLE h)).map ((Scheme.Modules.restrictFunctor U.ι).map a.hom) at hn
  apply Iso.ext
  simp only [AlgebraicGeometry.SheafCohomology.Projective.OpenRestrictionComposition.nativeOpenFrame, Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [← Category.assoc, ← hn]
  simp only [Category.assoc]

end

end OAI.RepresentationTheory.Theta.Geometric.FrameGlobalIsoRestriction
