/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/SheafDerivedGlobalSections.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ExtCocomplexHomology

/-! # Represented Derived Functor -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RepresentedDerivedFunctor.DerivedSections

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian _root_.CategoryTheory.Abelian.Ext
universe v u
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {G : C ⥤ AddCommGrpCat.{v}} [G.Additive]
variable {Z F : C}

def sectionsCocomplexHomologyAddEquivRightDerived
    [HasInjectiveResolutions C] (R : InjectiveResolution F) (n : ℕ) :
    ↑(((G.mapHomologicalComplex (.up ℕ)).obj R.cocomplex).homology n) ≃+
      ↑((G.rightDerived n).obj F) :=
  (R.isoRightDerivedObj G n).symm.addCommGroupIsoToAddEquiv

lemma sectionsCocomplexHomologyAddEquivRightDerived_naturality
    [HasInjectiveResolutions C]
    {F' : C} (R : InjectiveResolution F) (R' : InjectiveResolution F')
    (g : F ⟶ F') (φ : InjectiveResolution.Hom R R' g) (n : ℕ)
    (x : ↑(((G.mapHomologicalComplex (.up ℕ)).obj R.cocomplex).homology n)) :
    sectionsCocomplexHomologyAddEquivRightDerived R' n
        (((HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (.up ℕ) n).map
          ((G.mapHomologicalComplex (.up ℕ)).map φ.hom)).hom x) =
      ((G.rightDerived n).map g).hom
        (sectionsCocomplexHomologyAddEquivRightDerived R n x) := by
  let HN := HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (.up ℕ) n
  let fN := (G.mapHomologicalComplex (.up ℕ)).map φ.hom
  have h := InjectiveResolution.isoRightDerivedObj_inv_naturality g R R' φ.hom
    (by simpa using φ.ι_f_zero_comp_hom_f_zero) G n
  have hx := ConcreteCategory.congr_hom h x
  change (R'.isoRightDerivedObj G n).inv.hom ((HN.map fN).hom x) =
    ((G.rightDerived n).map g).hom ((R.isoRightDerivedObj G n).inv.hom x)
  exact hx.symm

/-- If an additive functor is represented by `Z`, then `Extⁿ(Z, -)` agrees with its
right-derived functor in degree `n`. -/
noncomputable def addEquivRightDerived
    [HasExt.{v} C] [HasInjectiveResolutions C]
    (G : C ⥤ AddCommGrpCat.{v}) [G.Additive] (Z F : C)
    (e : ∀ X : C, (Z ⟶ X) ≃+ ↑(G.obj X))
    (he : ∀ {X Y : C} (f : Z ⟶ X) (g : X ⟶ Y),
      e Y (f ≫ g) = G.map g (e X f)) (n : ℕ) :
    Ext.{v} Z F n ≃+ ↑((G.rightDerived n).obj F) :=
  let R := injectiveResolution F
  (ExtInjectiveHomology.DerivedSections.extAddEquivHomComplexHomology R n).trans
    ((ExtRepresentedHomology.DerivedSections.homComplexHomologyAddEquivSections e he R n).trans
      ((ExtCocomplexHomology.DerivedSections.sectionsCochainHomologyAddEquivCocomplex R n).trans
        (sectionsCocomplexHomologyAddEquivRightDerived R n)))

/-- The comparison between represented `Ext` and the right-derived functor is natural
in the derived variable. -/
theorem addEquivRightDerived_naturality
    [HasExt.{v} C] [HasInjectiveResolutions C]
    (G : C ⥤ AddCommGrpCat.{v}) [G.Additive] (Z : C)
    (e : ∀ X : C, (Z ⟶ X) ≃+ ↑(G.obj X))
    (he : ∀ {X Y : C} (a : Z ⟶ X) (b : X ⟶ Y),
      e Y (a ≫ b) = G.map b (e X a))
    {F F' : C} (f : F ⟶ F') (n : ℕ) (x : Ext.{v} Z F n) :
    addEquivRightDerived G Z F' e he n (((Ext.mk₀ f).postcomp Z (add_zero n)) x) =
      ((G.rightDerived n).map f).hom (addEquivRightDerived G Z F e he n x) := by
  let R := injectiveResolution F
  let R' := injectiveResolution F'
  let φ : InjectiveResolution.Hom R R' f :=
    { hom := InjectiveResolution.desc f R' R
      ι_f_zero_comp_hom_f_zero := by
        simpa using InjectiveResolution.desc_commutes_zero f R' R }
  change sectionsCocomplexHomologyAddEquivRightDerived R' n
      (ExtCocomplexHomology.DerivedSections.sectionsCochainHomologyAddEquivCocomplex R' n
        (ExtRepresentedHomology.DerivedSections.homComplexHomologyAddEquivSections e he R' n
          (ExtInjectiveHomology.DerivedSections.extAddEquivHomComplexHomology R' n (x.comp (Ext.mk₀ f) (add_zero n))))) =
    ((G.rightDerived n).map f).hom
      (sectionsCocomplexHomologyAddEquivRightDerived R n
        (ExtCocomplexHomology.DerivedSections.sectionsCochainHomologyAddEquivCocomplex R n
          (ExtRepresentedHomology.DerivedSections.homComplexHomologyAddEquivSections e he R n
            (ExtInjectiveHomology.DerivedSections.extAddEquivHomComplexHomology R n x))))
  rw [ExtInjectiveHomology.DerivedSections.extAddEquivHomComplexHomology_naturality R R' f φ n x]
  rw [ExtRepresentedHomology.DerivedSections.homComplexHomologyAddEquivSections_naturality e he R R' f φ n]
  rw [ExtCocomplexHomology.DerivedSections.sectionsCochainHomologyAddEquivCocomplex_naturality R R' f φ n]
  exact sectionsCocomplexHomologyAddEquivRightDerived_naturality R R' f φ n _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RepresentedDerivedFunctor.DerivedSections
