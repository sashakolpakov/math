import OAI.AlgebraicGeometry.Crystalline.Cohomology.GlobalCech
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineZariski.DerivedSections

/-! # Derived Section Ext -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.DerivedSectionExt.CrystallineDerivedSectionExt

noncomputable section

/-!
# Native derived sections and the original crystalline Ext modules

The comparison uses the specified coefficient action and the original
injective resolutions. On an actual open immersion it identifies the
derived Zariski section functor with the original crystalline groups
of that open, including the required coefficient-universe lift.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k)))

local notation "R" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.CoefficientRing p k
local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafInjectives.CrystallineSheafInjectives.Modules p k
local notation "G" => Sheaf.Γ (OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.topology p k X) V
local notation "L" => OAI.AlgebraicGeometry.Crystalline.Cohomology.GlobalCech.CrystallineGlobalCechCohomology.liftCoefficients p k

variable (F : Sheaf (Site.topology p k X)
  (ModuleCat.{u + 1} (Site.CoefficientRing p k))) (I : InjectiveResolution F)

def complexHomologyIso (n : ℕ) : (GlobalExtSections.CrystallineGlobalExtSections.complex p k X F I).homology n ≅
    ModuleCat.of R (Abelian.Ext (Site.coefficientSheaf p k X) F n) :=
  (HomologicalComplex.homologyFunctor _ _ n).mapIso (GlobalExtSections.CrystallineGlobalExtSections.extComplexIso p k X F I).symm ≪≫
    NumberTheory.PadicHodge.IntegralComparison.InjectiveSectionCohomology.homologyIso R (Site.coefficientSheaf p k X) I n

def derivedIso (n : ℕ) : (L).obj (((G).rightDerived n).obj F) ≅
    ModuleCat.of R (Abelian.Ext (Site.coefficientSheaf p k X) F n) :=
  (L).mapIso (I.isoRightDerivedObj G n) ≪≫
    (Cech.SheafExactness.CechSheafExactness.mapHomologyIso L
      (((G).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex) n).symm ≪≫
        complexHomologyIso p k X F I n

def structureIso (n : ℕ) : (L).obj (((G).rightDerived n).obj (Site.structureSheaf p k X)) ≅
    ModuleCat.of R (Site.integralCohomology p k X n) :=
  derivedIso p k X (Site.structureSheaf p k X) (injectiveResolution _) n

variable {X} {Y : Over (Spec (CommRingCat.of k))} (j : X ⟶ Y) [IsOpenImmersion j.left]

def openIso (n : ℕ) :
    (L).obj (((CrystallineZariski.SectionNaturality.CrystallineZariskiSectionNaturality.evaluation p k j).rightDerived n).obj
      (Site.structureSheaf p k Y)) ≅ ModuleCat.of R (Site.integralCohomology p k X n) :=
  (L).mapIso (CrystallineZariski.DerivedSections.CrystallineZariskiDerivedSections.structureIso p k j n) ≪≫ structureIso p k X n

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.DerivedSectionExt.CrystallineDerivedSectionExt
