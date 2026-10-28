import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineZariski.SectionNaturality
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ExactInjective
import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Derived Sections -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineZariski.DerivedSections.CrystallineZariskiDerivedSections

noncomputable section

/-!
# Derived Zariski sections compute native open crystalline cohomology

The natural section comparison identifies the entire complex obtained
from any injective crystalline resolution. Exact open restriction
preserves its injectives, so the derived section functors agree in all
degrees with native derived global sections on the open crystalline site.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  {X Y : Over (Spec (CommRingCat.of k))} (j : X ⟶ Y) [IsOpenImmersion j.left]

local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafInjectives.CrystallineSheafInjectives.Modules p k
local notation "NativeTopology" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.topology p k Y
local notation "SmallTopology" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.topology p k X
local notation "Restriction" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineOpen.SheafExactness.CrystallineOpenSheafExactness.restriction p k j
local notation "Evaluation" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineZariski.SectionNaturality.CrystallineZariskiSectionNaturality.evaluation p k j
local notation "Sections" => Sheaf.Γ SmallTopology V

local instance sections_additive : (Sections).Additive :=
  Functor.additive_of_preserves_binary_products _

instance evaluation_additive : (Evaluation).Additive :=
  Functor.additive_of_iso (SectionNaturality.CrystallineZariskiSectionNaturality.globalSectionsIso p k j).symm

variable (F : Sheaf (Site.topology p k Y)
  (ModuleCat.{u + 1} (Site.CoefficientRing p k))) (I : InjectiveResolution F)

def complexIso : ((Evaluation).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex ≅
    ((Sections).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (ExactInjective.ExactInjectiveResolution.map Restriction I).cocomplex :=
  HomologicalComplex.Hom.isoOfComponents
    (fun _n => (SectionNaturality.CrystallineZariskiSectionNaturality.globalSectionsIso p k j).app (I.cocomplex.X _n))
    (fun _m _n _ => ((SectionNaturality.CrystallineZariskiSectionNaturality.globalSectionsIso p k j).hom.naturality
      (I.cocomplex.d _m _n)).symm)

def derivedIso (n : ℕ) : ((Evaluation).rightDerived n).obj F ≅
    ((Sections).rightDerived n).obj ((Restriction).obj F) :=
  I.isoRightDerivedObj Evaluation n ≪≫
    (HomologicalComplex.homologyFunctor V (ComplexShape.up ℕ) n).mapIso (complexIso p k j F I) ≪≫
      ((ExactInjective.ExactInjectiveResolution.map Restriction I).isoRightDerivedObj Sections n).symm

def structureIso (n : ℕ) :
    ((Evaluation).rightDerived n).obj (Site.structureSheaf p k Y) ≅
      ((Sections).rightDerived n).obj (Site.structureSheaf p k X) :=
  derivedIso p k j (Site.structureSheaf p k Y) (injectiveResolution _) n ≪≫
    ((Sections).rightDerived n).mapIso (CrystallineOpen.Sheaves.CrystallineOpenSheaves.structureIso p k j)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineZariski.DerivedSections.CrystallineZariskiDerivedSections
