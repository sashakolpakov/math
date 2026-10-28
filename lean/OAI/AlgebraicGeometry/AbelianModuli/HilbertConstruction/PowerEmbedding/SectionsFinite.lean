import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.TwistingSectionsFinite
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RelativeProjective.TwistingBundle

/-! # Sections Finite -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A positive power retained by an actual projective embedding has finite-dimensional sections in every nonnegative further power. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}} (p : X ⟶ Spec (.of K))
variable [Flat p] [LocallyOfFinitePresentation p] {L : Line.Bundles.LineBundle X}

theorem Power.ProjectiveEmbeddings.PowerProjectiveEmbedding.powerSections_finite (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding L p) (d : ℕ) :
    Module.Finite K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj (E.power.tensorPower d).sheaf) := by
  have : IsClosedImmersion (SectionsProjectiveMorphism.sectionProjectiveMorphism p E.sections E.covers).left := E.closedImmersion
  have : Flat (Over.mk p).hom := inferInstanceAs (Flat p)
  have : LocallyOfFinitePresentation (Over.mk p).hom := inferInstanceAs (LocallyOfFinitePresentation p)
  have hf := Embedded.TwistingSectionsFinite.relativeEmbedding_twistingPowerSections_finite
    (SectionsProjectiveMorphism.sectionProjectiveMorphism p E.sections E.covers) d
  exact (Module.Finite.equiv_iff (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsIso p
    ((TensorPower.Maps.tensorPowerFunctor X d).mapIso (E.twistingBundleIso p)))).mp hf

theorem Power.ProjectiveEmbeddings.PowerProjectiveEmbedding.degreePowerSections_finite (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding L p) (d : ℕ) :
    Module.Finite K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj ((L.tensorPower E.degree).tensorPower d).sheaf) := by
  let e := (E.isPower.unique (L.tensorPower_isTensorPower E.degree)).some
  exact (Module.Finite.equiv_iff (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsIso p
    ((TensorPower.Maps.tensorPowerFunctor X d).mapIso e))).mp (E.powerSections_finite p d)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
