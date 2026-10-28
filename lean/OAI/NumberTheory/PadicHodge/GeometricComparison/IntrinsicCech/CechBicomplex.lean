import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.GlobalSectionFunctor
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.SectionsTotal

/-! # Cech Bicomplex -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.CechBicomplex.IntrinsicCechBicomplex

noncomputable section

/-! The direct Čech cochain bicomplex is canonically the actual global native Čech section calculation. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
  {ι : Type} (U : ι → X.left.Opens) (K : CochainComplex (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X) ℕ)

local instance : (SectionUnit.IntrinsicCechSectionUnit.sheafSections R X.left U).Additive :=
  GlobalSectionFunctor.IntrinsicCechGlobalSectionFunctor.sheafSections_additive R X U

def bicomplex : HomologicalComplex₂ (ModuleCat.{0} R) (.up ℕ) (.up ℕ) :=
  ((Cech.CechSheaf.functor R X U).mapHomologicalComplex (.up ℕ)).obj K

def sectionIso : SectionsTotal.IntrinsicCechSectionsTotal.bicomplex R X.left U K ≅ bicomplex R X U K :=
  (NatIso.mapHomologicalComplex (GlobalSectionFunctor.IntrinsicCechGlobalSectionFunctor.iso R X U) (.up ℕ)).app K

def integerTotal : CochainComplex (ModuleCat.{0} R) ℤ :=
  ((bicomplex R X U K).total (.up ℕ)).extend ComplexShape.embeddingUpNat

def iso : integerTotal R X U K ≅ Terms.IntrinsicCechComparison.sections R X.left U K :=
  (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{0} R)).mapIso
    (HomologicalComplex₂.total.mapIso (sectionIso R X U K).symm (.up ℕ)) ≪≫
      SectionsTotal.IntrinsicCechSectionsTotal.iso R X.left U K

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.CechBicomplex.IntrinsicCechBicomplex
