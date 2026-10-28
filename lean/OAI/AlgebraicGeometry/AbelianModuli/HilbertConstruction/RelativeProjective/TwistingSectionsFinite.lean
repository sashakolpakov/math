import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.ProjectiveTwistingSectionsFinite
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.TwistingAffinePullback

/-! # Twisting Sections Finite -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RelativeProjective.TwistingSectionsFinite

noncomputable section

/-! Finiteness of actual twisting sections is compatible with relative projective space over any Noetherian affine spectrum. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {n : ℕ}

def identityAffineProjectiveChartIso :
    Projective.ProjectivePresentations.affineProjectiveSpace R n ≅ Projective.ProjectivePresentations.projectiveSpaceOver (Spec (.of R)) n := by
  have : IsIso (AffineProjective.Charts.affineProjectiveChartMap (𝟙 (Spec (.of R))) n) :=
    (AffineProjective.Charts.affineProjectiveChartMap_isPullback (𝟙 (Spec (.of R))) n).isIso_fst_of_isIso
  exact Over.isoMk (asIso (AffineProjective.Charts.affineProjectiveChartMap (𝟙 (Spec (.of R))) n))
    ((AffineProjective.Charts.affineProjectiveChartMap_over (𝟙 (Spec (.of R))) n).trans (Category.comp_id _))

variable {X : Over (Spec (.of R))} (i : X ⟶ Projective.ProjectivePresentations.projectiveSpaceOver (Spec (.of R)) n)

def relativeEmbeddingAffineMap : X ⟶ Projective.ProjectivePresentations.affineProjectiveSpace R n :=
  i ≫ identityAffineProjectiveChartIso.inv

instance relativeEmbeddingAffineMap_closed [IsClosedImmersion i.left] :
    IsClosedImmersion (relativeEmbeddingAffineMap i).left := by
  have : IsIso (identityAffineProjectiveChartIso (R := R) (n := n)).inv.left :=
    (Over.forget _).map_isIso identityAffineProjectiveChartIso.inv
  exact inferInstanceAs (IsClosedImmersion
    (i.left ≫ (identityAffineProjectiveChartIso (R := R) (n := n)).inv.left))

def relativeEmbeddingAffineTwistingIso :
    ((Section.AbsoluteTwistingBundle.affineProjectiveTwistingBundle R n).pullback (relativeEmbeddingAffineMap i).left).sheaf ≅
      ((TwistingBundle.relativeProjectiveTwistingBundle (Spec (.of R)) n).pullback i.left).sheaf := by
  have he' : relativeEmbeddingAffineMap i ≫ identityAffineProjectiveChartIso.hom = i := by
    dsimp only [relativeEmbeddingAffineMap]
    simp
  have he : (relativeEmbeddingAffineMap i).left ≫ AffineProjective.Charts.affineProjectiveChartMap (𝟙 (Spec (.of R))) n =
      i.left := congrArg Over.Hom.left he'
  exact (Scheme.Modules.pullback (relativeEmbeddingAffineMap i).left).mapIso
      (Relative.TwistingAffinePullback.relativeProjectiveTwistingBundle_affineIso (𝟙 (Spec (.of R))) n).symm ≪≫
    (Scheme.Modules.pullbackComp (relativeEmbeddingAffineMap i).left
      (AffineProjective.Charts.affineProjectiveChartMap (𝟙 (Spec (.of R))) n)).app
      (TwistingBundle.relativeProjectiveTwistingBundle (Spec (.of R)) n).sheaf ≪≫
    (Scheme.Modules.pullbackCongr he).app (TwistingBundle.relativeProjectiveTwistingBundle (Spec (.of R)) n).sheaf

theorem relativeEmbedding_twistingPowerSections_finite_noetherian
    [IsNoetherianRing R] [IsClosedImmersion i.left] (d : ℕ) :
    Module.Finite R ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor X.hom).obj
      (((TwistingBundle.relativeProjectiveTwistingBundle (Spec (.of R)) n).pullback i.left).tensorPower d).sheaf) := by
  have : Module.Finite R ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor X.hom).obj
      ((TensorPower.Maps.tensorPowerFunctor X.left d).obj
        ((Section.AbsoluteTwistingBundle.affineProjectiveTwistingBundle R n).pullback (relativeEmbeddingAffineMap i).left).sheaf)) :=
    Closed.ProjectiveTwistingSectionsFinite.ClosedProjectiveEmbedding.twistingPowerSections_finite (relativeEmbeddingAffineMap i) d
  exact Module.Finite.equiv (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsIso X.hom
    ((TensorPower.Maps.tensorPowerFunctor X.left d).mapIso (relativeEmbeddingAffineTwistingIso i)))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RelativeProjective.TwistingSectionsFinite
