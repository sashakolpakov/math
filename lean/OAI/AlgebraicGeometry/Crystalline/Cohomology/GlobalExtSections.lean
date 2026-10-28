import OAI.AlgebraicGeometry.Crystalline.Cohomology.Module.SheafGlobalSections
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineZariski.GlobalSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.InjectiveSectionCohomology

/-! # Global Ext Sections -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.GlobalExtSections.CrystallineGlobalExtSections

noncomputable section

/-!
# The original crystalline Ext groups from actual global sections

The constant coefficient sheaf represents coefficient-linear global
sections. Applying this natural identification to the original injective
resolution computes its Ext groups with their specified scalar action.
-/

open _root_.CategoryTheory

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (AlgebraicGeometry.Spec (CommRingCat.of k)))

local notation "R" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.CoefficientRing p k
local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafInjectives.CrystallineSheafInjectives.Modules p k
local notation "J" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.topology p k X

def sections : Sheaf J V ⥤ ModuleCat.{u + 2} R :=
  Sheaf.Γ J V ⋙ ModuleCat.uliftFunctor.{u + 2, u + 1} R

instance sections_additive : (sections p k X).Additive := by
  unfold sections
  infer_instance

def complex (F : Sheaf (Site.topology p k X)
    (ModuleCat.{u + 1} (Site.CoefficientRing p k))) (I : InjectiveResolution F) :
    CochainComplex (ModuleCat.{u + 2} R) ℕ :=
  ((sections p k X).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex

def extComplexIso (F : Sheaf (Site.topology p k X)
    (ModuleCat.{u + 1} (Site.CoefficientRing p k))) (I : InjectiveResolution F) :
    NumberTheory.PadicHodge.IntegralComparison.InjectiveSectionCohomology.complex R (Site.coefficientSheaf p k X) I ≅
      complex p k X F I :=
  (NatIso.mapHomologicalComplex (Module.SheafGlobalSections.ModuleSheafGlobalSections.iso.{u + 1, u, u + 1, u + 2} R J)
    (ComplexShape.up ℕ)).app I.cocomplex

def homologyIso (I : InjectiveResolution (Site.structureSheaf p k X)) (n : ℕ) :
    (complex p k X (Site.structureSheaf p k X) I).homology n ≅
      ModuleCat.of R (Site.integralCohomology p k X n) :=
  (HomologicalComplex.homologyFunctor _ _ n).mapIso
    (extComplexIso p k X (Site.structureSheaf p k X) I).symm ≪≫
      NumberTheory.PadicHodge.IntegralComparison.InjectiveSectionCohomology.homologyIso R (Site.coefficientSheaf p k X) I n

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.GlobalExtSections.CrystallineGlobalExtSections
