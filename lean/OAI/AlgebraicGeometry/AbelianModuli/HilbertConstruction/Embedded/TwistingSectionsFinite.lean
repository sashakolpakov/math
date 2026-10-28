import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.EmbeddingIntrinsic
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveTwisting.SectionsFinite

/-! # Twisting Sections Finite -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Every nonnegative power of the restricted projective twisting bundle has finite-dimensional actual global sections, with no eventual-degree restriction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {n : ℕ}

theorem Closed.Families.FlatClosedFamily.twistingPowerSections_finite
    (F : Closed.Families.FlatClosedFamily (Projective.ProjectivePresentations.affineProjectiveSpace K n)) (d : ℕ) :
    Module.Finite K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor F.scheme.hom).obj (F.twistingBundle.tensorPower d).sheaf) := by
  have := ProjectiveTwisting.SectionsFinite.projectiveTwistingSections_finite F.homogeneousIdeal d
  have hf : Module.Finite K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor (Projective.EmbeddingBaseChange.homogeneousProjectiveFamily F.homogeneousIdeal).hom).obj
      ((ProjectiveTwisting.Bundle.projectiveTwistingBundle F.homogeneousIdeal 1).tensorPower d).sheaf) :=
    Module.Finite.equiv (Projective.IntrinsicPolynomial.projectiveTwistingPowerSectionsIso F.homogeneousIdeal d).symm
  let e := (Intrinsic.LineBundleSections.lineBundlePowerSectionsOverIso (R := K) F.homogeneousFamilyIso
    F.twistingBundle (ProjectiveTwisting.Bundle.projectiveTwistingBundle F.homogeneousIdeal 1) F.homogeneousTwistingBundleIso d).symm
  exact @Module.Finite.equiv K _ _ _ _ _ _ _ hf e

theorem Closed.Families.FlatClosedFamily.relativeTwistingPowerSections_finite
    (F : Closed.Families.FlatClosedFamily (Projective.ProjectivePresentations.projectiveSpaceOver (Spec (.of K)) n)) (d : ℕ) :
    Module.Finite K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor F.scheme.hom).obj
      (F.relativeTwistingBundle.tensorPower d).sheaf) := by
  have := (F.affineProjectivePullback (𝟙 _)).twistingPowerSections_finite d
  exact Module.Finite.equiv (Intrinsic.LineBundleSections.lineBundlePowerSectionsOverIso (R := K) F.identityAffineFamilyIso
    F.relativeTwistingBundle (F.affineProjectivePullback (𝟙 _)).twistingBundle
    F.identityAffineTwistingBundleIso d).symm

theorem Embedded.TwistingSectionsFinite.relativeEmbedding_twistingPowerSections_finite
    {A : Over (Spec (.of K))} (i : A ⟶ Projective.ProjectivePresentations.projectiveSpaceOver (Spec (.of K)) n)
    [IsClosedImmersion i.left] [Flat A.hom] [LocallyOfFinitePresentation A.hom] (d : ℕ) :
    Module.Finite K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor A.hom).obj
      (((RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle (Spec (.of K)) n).pullback i.left).tensorPower d).sheaf) := by
  have := (Closed.Families.FlatClosedFamily.ofEmbedding i).relativeTwistingPowerSections_finite d
  exact Module.Finite.equiv (Intrinsic.LineBundleSections.lineBundlePowerSectionsOverIso (R := K) (Closed.Families.FlatClosedFamily.ofEmbeddingIso i)
    (Closed.Families.FlatClosedFamily.ofEmbedding i).relativeTwistingBundle
    ((RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle (Spec (.of K)) n).pullback i.left)
    (Relative.EmbeddingIntrinsic.relativeEmbeddingTwistingBundleIso i) d)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
