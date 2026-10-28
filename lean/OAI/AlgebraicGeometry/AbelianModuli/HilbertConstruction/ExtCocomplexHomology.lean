/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/SheafDerivedGlobalSections.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ExtRepresentedHomology

/-! # Ext Cocomplex Homology -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ExtCocomplexHomology.DerivedSections

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian _root_.CategoryTheory.Abelian.Ext
universe v u
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {G : C ⥤ AddCommGrpCat.{v}} [G.Additive]
variable {Z F : C}

def sectionsCochainHomologyAddEquivCocomplex
    (R : InjectiveResolution F) (n : ℕ) :
    ↑(((G.mapHomologicalComplex (.up ℤ)).obj R.cochainComplex).homology n) ≃+
      ↑(((G.mapHomologicalComplex (.up ℕ)).obj R.cocomplex).homology n) :=
  ((HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (.up ℤ) n).mapIso
      (MappedComplexExtensionIso.DerivedSections.mapExtendIso R.cocomplex)).addCommGroupIsoToAddEquiv.trans
    (((G.mapHomologicalComplex (.up ℕ)).obj R.cocomplex).extendHomologyIso
      ComplexShape.embeddingUpNat
      (show ComplexShape.embeddingUpNat.f n = (n : ℤ) from rfl)).addCommGroupIsoToAddEquiv

lemma sectionsCochainHomologyAddEquivCocomplex_naturality
    {F' : C} (R : InjectiveResolution F) (R' : InjectiveResolution F')
    (g : F ⟶ F') (φ : InjectiveResolution.Hom R R' g) (n : ℕ)
    (x : ↑(((G.mapHomologicalComplex (.up ℤ)).obj R.cochainComplex).homology n)) :
    sectionsCochainHomologyAddEquivCocomplex R' n
        (((HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (.up ℤ) n).map
          ((G.mapHomologicalComplex (.up ℤ)).map φ.hom')).hom x) =
      ((HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (.up ℕ) n).map
        ((G.mapHomologicalComplex (.up ℕ)).map φ.hom)).hom
          (sectionsCochainHomologyAddEquivCocomplex R n x) := by
  let HZ := HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (.up ℤ) n
  let HN := HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (.up ℕ) n
  let fN := (G.mapHomologicalComplex (.up ℕ)).map φ.hom
  let fE := HomologicalComplex.extendMap fN ComplexShape.embeddingUpNat
  have hmap :
      (G.mapHomologicalComplex (.up ℤ)).map φ.hom' ≫ (MappedComplexExtensionIso.DerivedSections.mapExtendIso R'.cocomplex).hom =
        (MappedComplexExtensionIso.DerivedSections.mapExtendIso R.cocomplex).hom ≫ fE := by
    simpa [InjectiveResolution.cochainComplex, InjectiveResolution.Hom.hom', fN, fE] using
      MappedComplexExtensionNaturality.DerivedSections.mapExtendIso_naturality (G := G) φ.hom
  have hmapH :
      HZ.map ((G.mapHomologicalComplex (.up ℤ)).map φ.hom') ≫
          HZ.map (MappedComplexExtensionIso.DerivedSections.mapExtendIso R'.cocomplex).hom =
        HZ.map (MappedComplexExtensionIso.DerivedSections.mapExtendIso R.cocomplex).hom ≫ HZ.map fE := by
    exact (HZ.map_comp _ _).symm.trans
      ((congrArg HZ.map hmap).trans (HZ.map_comp _ _))
  have hext : HZ.map fE ≫
        (((G.mapHomologicalComplex (.up ℕ)).obj R'.cocomplex).extendHomologyIso
          ComplexShape.embeddingUpNat rfl).hom =
      (((G.mapHomologicalComplex (.up ℕ)).obj R.cocomplex).extendHomologyIso
          ComplexShape.embeddingUpNat rfl).hom ≫ HN.map fN := by
    change HomologicalComplex.homologyMap fE (n : ℤ) ≫
        (((G.mapHomologicalComplex (.up ℕ)).obj R'.cocomplex).extendHomologyIso
          ComplexShape.embeddingUpNat rfl).hom =
      (((G.mapHomologicalComplex (.up ℕ)).obj R.cocomplex).extendHomologyIso
          ComplexShape.embeddingUpNat rfl).hom ≫ HomologicalComplex.homologyMap fN n
    exact HomologicalComplex.extendHomologyIso_hom_naturality fN
      ComplexShape.embeddingUpNat (show ComplexShape.embeddingUpNat.f n = (n : ℤ) from rfl)
  have htotal :
      (HZ.map ((G.mapHomologicalComplex (.up ℤ)).map φ.hom') ≫
          HZ.map (MappedComplexExtensionIso.DerivedSections.mapExtendIso R'.cocomplex).hom) ≫
            (((G.mapHomologicalComplex (.up ℕ)).obj R'.cocomplex).extendHomologyIso
              ComplexShape.embeddingUpNat rfl).hom =
        (HZ.map (MappedComplexExtensionIso.DerivedSections.mapExtendIso R.cocomplex).hom ≫
          (((G.mapHomologicalComplex (.up ℕ)).obj R.cocomplex).extendHomologyIso
            ComplexShape.embeddingUpNat rfl).hom) ≫ HN.map fN := by
    let A := HZ.map ((G.mapHomologicalComplex (.up ℤ)).map φ.hom')
    let B := HZ.map (MappedComplexExtensionIso.DerivedSections.mapExtendIso (G := G) R'.cocomplex).hom
    let C₀ := HZ.map (MappedComplexExtensionIso.DerivedSections.mapExtendIso (G := G) R.cocomplex).hom
    let D := HZ.map fE
    let E' := (((G.mapHomologicalComplex (.up ℕ)).obj
      R'.cocomplex).extendHomologyIso ComplexShape.embeddingUpNat
        (show ComplexShape.embeddingUpNat.f n = (n : ℤ) from rfl)).hom
    let E := (((G.mapHomologicalComplex (.up ℕ)).obj
      R.cocomplex).extendHomologyIso ComplexShape.embeddingUpNat
        (show ComplexShape.embeddingUpNat.f n = (n : ℤ) from rfl)).hom
    let F₀ := HN.map fN
    have hmapH' : A ≫ B = C₀ ≫ D := hmapH
    have hext' : D ≫ E' = E ≫ F₀ := hext
    change (A ≫ B) ≫ E' = (C₀ ≫ E) ≫ F₀
    have h₀ := congrArg (fun q ↦ q ≫ E') hmapH'
    have h₁ := Category.assoc C₀ D E'
    have h₂ := congrArg (fun q ↦ C₀ ≫ q) hext'
    have h₃ := (Category.assoc C₀ E F₀).symm
    exact h₀.trans (h₁.trans (h₂.trans h₃))
  have hx := ConcreteCategory.congr_hom htotal x
  change (((G.mapHomologicalComplex (.up ℕ)).obj R'.cocomplex).extendHomologyIso
      ComplexShape.embeddingUpNat rfl).hom.hom
        ((HZ.map (MappedComplexExtensionIso.DerivedSections.mapExtendIso R'.cocomplex).hom).hom
          ((HZ.map ((G.mapHomologicalComplex (.up ℤ)).map φ.hom')).hom x)) =
    (HN.map fN).hom
      ((((G.mapHomologicalComplex (.up ℕ)).obj R.cocomplex).extendHomologyIso
        ComplexShape.embeddingUpNat rfl).hom.hom
          ((HZ.map (MappedComplexExtensionIso.DerivedSections.mapExtendIso R.cocomplex).hom).hom x))
  exact hx

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ExtCocomplexHomology.DerivedSections
