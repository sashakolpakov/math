import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.GlobalSectionFunctor
import OAI.AlgebraicGeometry.Crystalline.Cohomology.MixedCech.ComplexResolution
import OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.TotalIso

/-! # Section Total -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.SectionTotal.CechSectionTotal

noncomputable section

/-! # The direct Čech total is the actual global-section complex of the Čech sheaf total -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

universe u

variable (R : Type u) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
  {ι : Type u} (U : ι → X.left.Opens) (K : CochainComplex (DeRhamGlobalId.DeRhamGlobal.Sheaves R X) ℕ)

local instance : HasCoproducts.{0} (DeRhamGlobalId.DeRhamGlobal.Sheaves R X) := ZariskiColimitsCore.ZariskiColimits.coproducts R X.left
local instance : (SectionHypercohomologyInv.SectionHypercohomology.sections R (TopCat.of X.left)).Additive where
  map_add := rfl
local instance : (MixedCech.Functor.MixedCechFunctor.sheafFunctor R X.left U).Additive :=
  MixedCech.Functor.MixedCechFunctor.sheaf_additive R X.left U
local instance : (SectionUnit.CechSectionUnit.sheafSections R X.left U).Additive :=
  GlobalSectionFunctor.CechGlobalSectionFunctor.sheafSections_additive R X U

def sheafBicomplex :=
  NumberTheory.PadicHodge.GeometricComparison.Functor.ResolutionBicomplex.FunctorResolutionBicomplex.bicomplex (MixedCech.Functor.MixedCechFunctor.sheafFunctor R X.left U) K

def sectionBicomplex : HomologicalComplex₂ (ModuleCat.{u} R) (.up ℕ) (.up ℕ) :=
  Comparison.Betti.TotalComplexFunctor.mapBicomplex (SectionHypercohomologyInv.SectionHypercohomology.sections R (TopCat.of X.left)) (sheafBicomplex R X U K)

def directBicomplex : HomologicalComplex₂ (ModuleCat.{u} R) (.up ℕ) (.up ℕ) :=
  ((NumberTheory.PadicHodge.GeometricComparison.Cech.CechSheaf.functor R X U).mapHomologicalComplex (.up ℕ)).obj K

def bicomplexIso : sectionBicomplex R X U K ≅ directBicomplex R X U K :=
  (NatIso.mapHomologicalComplex (GlobalSectionFunctor.CechGlobalSectionFunctor.iso R X U) (.up ℕ)).app K

def directTotal : CochainComplex (ModuleCat.{u} R) ℤ :=
  ((directBicomplex R X U K).total (.up ℕ)).extend ComplexShape.embeddingUpNat

def iso : directTotal R X U K ≅
    SectionHypercohomologyInv.SectionHypercohomology.sectionComplex R (TopCat.of X.left)
      (MixedCech.ComplexResolution.MixedCechComplexResolution.integerTotal R X.left U K) :=
  (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} R)).mapIso
    (HomologicalComplex₂.total.mapIso (bicomplexIso R X U K).symm (.up ℕ)) ≪≫
      NumberTheory.PadicHodge.GeometricComparison.Finite.TotalIso.FiniteTotalExtension.iso (SectionHypercohomologyInv.SectionHypercohomology.sections R (TopCat.of X.left))
        (sheafBicomplex R X U K)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.SectionTotal.CechSectionTotal
