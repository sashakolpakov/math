import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.SectionsTotal
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.GlobalSectionFunctor
import OAI.NumberTheory.PadicHodge.GeometricComparison.TotalFinite

/-! # Section Total Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.SectionTotalNaturality.IntrinsicCechSectionTotalNaturality

noncomputable section

/-! The native section-total comparison is natural in the original complex of sheaves. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
  {ι : Type} (U : ι → X.left.Opens)

abbrev Sheaves := Bicomplex.IntrinsicCechBicomplex.Sheaves R X.left

local instance : HasCoproducts.{0} (Sheaves R X) := Instances.IntrinsicCechInstances.hasCoproducts R X.left
local instance : (Functor.IntrinsicCechFunctor.sheafFunctor R X.left U).Additive :=
  Instances.IntrinsicCechInstances.additive R X.left U
local instance : (Section.Hypercohomology.SectionHypercohomology.sections R (TopCat.of X.left)).Additive where
  map_add := rfl

def sectionMap {K L : CochainComplex (Sheaves R X) ℕ} (φ : K ⟶ L) :
    Terms.IntrinsicCechComparison.sections R X.left U K ⟶ Terms.IntrinsicCechComparison.sections R X.left U L :=
  ((Section.Hypercohomology.SectionHypercohomology.sections R (TopCat.of X.left)).mapHomologicalComplex (.up ℤ)).map
    (Terms.IntrinsicCechComparison.totalMap R X.left U φ)

theorem naturality {K L : CochainComplex (Sheaves R X) ℕ} (φ : K ⟶ L) :
    (TotalFinite.IntegerTotalFunctor.functor (ModuleCat.{0} R)).map
        (((SectionUnit.IntrinsicCechSectionUnit.sheafSections R X.left U).mapHomologicalComplex (.up ℕ)).map φ) ≫
      (SectionsTotal.IntrinsicCechSectionsTotal.iso R X.left U L).hom =
    (SectionsTotal.IntrinsicCechSectionsTotal.iso R X.left U K).hom ≫ sectionMap R X U φ :=
  TotalFinite.FiniteTotalExtensionNaturality.naturality (Section.Hypercohomology.SectionHypercohomology.sections R (TopCat.of X.left))
    (((Functor.IntrinsicCechFunctor.sheafFunctor R X.left U).mapHomologicalComplex (.up ℕ)).map φ)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.SectionTotalNaturality.IntrinsicCechSectionTotalNaturality
