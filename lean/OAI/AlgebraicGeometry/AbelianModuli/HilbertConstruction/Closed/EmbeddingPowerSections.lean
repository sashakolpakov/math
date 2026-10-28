import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PowerEmbedding.SectionsFinite
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.PowerBaseChange

/-! # Embedding Power Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Restricting a projectively embedded line-bundle power to any closed subscheme over a field preserves finiteness of its nonnegative power section spaces. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {X Y : Scheme.{u}} (p : X ⟶ Spec (.of K))
variable {L : Line.Bundles.LineBundle X} (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding L p)

theorem Power.ProjectiveEmbeddings.PowerProjectiveEmbedding.closedPullbackPowerSections_finite (i : Y ⟶ X)
    [IsClosedImmersion i] [Flat (i ≫ p)] [LocallyOfFinitePresentation (i ≫ p)] (d : ℕ) :
    Module.Finite K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor (i ≫ p)).obj
      ((E.power.pullback i).tensorPower d).sheaf) := by
  let j := SectionsProjectiveMorphism.sectionProjectiveMorphism p E.sections E.covers
  let k : Over.mk (i ≫ p) ⟶ Projective.ProjectivePresentations.projectiveSpaceOver (Spec (.of K)) E.dimension :=
    Over.homMk (i ≫ j.left) ((Category.assoc _ _ _).trans (congrArg (fun f => i ≫ f) j.w))
  have : IsClosedImmersion j.left := E.closedImmersion
  have : IsClosedImmersion k.left := inferInstanceAs (IsClosedImmersion (i ≫ j.left))
  have : Flat (Over.mk (i ≫ p)).hom := inferInstanceAs (Flat (i ≫ p))
  have : LocallyOfFinitePresentation (Over.mk (i ≫ p)).hom := inferInstanceAs (LocallyOfFinitePresentation (i ≫ p))
  let e : ((RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle (Spec (.of K)) E.dimension).pullback k.left).sheaf ≅
      (E.power.pullback i).sheaf :=
    (Scheme.Modules.pullbackComp i j.left).symm.app
      (RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle (Spec (.of K)) E.dimension).sheaf ≪≫
      (Scheme.Modules.pullback i).mapIso (E.twistingBundleIso p)
  exact (Module.Finite.equiv_iff (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsIso (i ≫ p)
    ((TensorPower.Maps.tensorPowerFunctor Y d).mapIso e))).mp (Embedded.TwistingSectionsFinite.relativeEmbedding_twistingPowerSections_finite k d)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
