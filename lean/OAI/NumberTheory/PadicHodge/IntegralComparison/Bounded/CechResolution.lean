import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.ZariskiAdjunction
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionGlobal
import OAI.NumberTheory.PadicHodge.IntegralComparison.ZariskiCechSections

/-! # Cech Resolution -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.CechResolution

noncomputable section

/-!
# IntegralComparison: finite Čech descent computes original bounded crystalline Ext
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {Y : Scheme.{u}} (fY : Y ⟶ Spec (CommRingCat.of B)) (n : ℕ)
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf
    (p := p) (J := J) (δ := δ) fY n))

def imageComplex : CochainComplex
    (Sheaf (Opens.grothendieckTopology Y) (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))) ℕ :=
  ((BoundedOpen.SectionSheaf.functor fY n).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex

theorem image_injective (q : ℕ) : Injective ((imageComplex fY n I).X q) := by
  let : Injective (I.cocomplex.X q) := I.injective q
  exact (BoundedOpen.SectionSheaf.functor fY n).injective_obj (I.cocomplex.X q)

variable {ι : Type u} [Finite ι] (U : ι → Y.Opens)

def smallTotal : CochainComplex (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B))) ℕ :=
  ZariskiCechSections.total (Crystalline.ExactRestriction.Coeff (B := B)) Y U (imageComplex fY n I)

def total : CochainComplex (ModuleCat.{u + 2} (Crystalline.ExactRestriction.Coeff (B := B))) ℕ :=
  ((ModuleCat.uliftFunctor.{u + 2, u + 1} (Crystalline.ExactRestriction.Coeff (B := B))).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (smallTotal fY n I U)

def sourceIso :
    (((ModuleCat.uliftFunctor.{u + 2, u + 1} (Crystalline.ExactRestriction.Coeff (B := B))).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (((ZariskiCechSections.sections (Crystalline.ExactRestriction.Coeff (B := B)) Y).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (imageComplex fY n I))) ≅
      (((BoundedOpen.SectionComplex.evaluation (B := B) (⊤ : Y.Opens)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (BoundedOpen.SectionComplex.complex fY n I)) := Iso.refl _

def comparison :
    (((BoundedOpen.SectionComplex.evaluation (B := B) (⊤ : Y.Opens)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (BoundedOpen.SectionComplex.complex fY n I)) ⟶ total fY n I U :=
  (sourceIso fY n I).inv ≫
    ((ModuleCat.uliftFunctor.{u + 2, u + 1} (Crystalline.ExactRestriction.Coeff (B := B))).mapHomologicalComplex (ComplexShape.up ℕ)).map
      (ZariskiCechSections.comparison (Crystalline.ExactRestriction.Coeff (B := B)) Y U (imageComplex fY n I))

theorem comparison_quasiIso (hU : iSup U = ⊤) : QuasiIso (comparison fY n I U) := by
  have : QuasiIso (ZariskiCechSections.comparison (Crystalline.ExactRestriction.Coeff (B := B)) Y U (imageComplex fY n I)) :=
    ZariskiCechSections.comparison_quasiIso (Crystalline.ExactRestriction.Coeff (B := B)) Y U (imageComplex fY n I) hU
      (image_injective fY n I)
  have hm : QuasiIso
      (((ModuleCat.uliftFunctor.{u + 2, u + 1} (Crystalline.ExactRestriction.Coeff (B := B))).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (ZariskiCechSections.comparison (Crystalline.ExactRestriction.Coeff (B := B)) Y U (imageComplex fY n I))) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology
      (ZariskiCechSections.comparison (Crystalline.ExactRestriction.Coeff (B := B)) Y U (imageComplex fY n I))
      (ModuleCat.uliftFunctor.{u + 2, u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))
  exact quasiIso_comp (sourceIso fY n I).inv _ (hφ' := hm)

def homologyIso (hU : iSup U = ⊤) (i : ℕ) : (total fY n I U).homology i ≅
    ModuleCat.of (Crystalline.ExactRestriction.Coeff (B := B))
      (BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) fY n i) := by
  have : QuasiIso (comparison fY n I U) := comparison_quasiIso fY n I U hU
  exact (isoOfQuasiIsoAt (comparison fY n I U) i).symm ≪≫ BoundedOpen.SectionGlobal.homologyIso fY n I i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.CechResolution
