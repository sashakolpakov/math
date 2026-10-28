/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/SheafDerivedGlobalSections.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ExtInjectiveHomology

/-! # Ext Represented Homology -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ExtRepresentedHomology.DerivedSections

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian _root_.CategoryTheory.Abelian.Ext
universe v u
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {G : C ⥤ AddCommGrpCat.{v}} [G.Additive]
variable {Z F : C}

def homComplexHomologyAddEquivSections
    (e : ∀ X : C, (Z ⟶ X) ≃+ ↑(G.obj X))
    (he : ∀ {X Y : C} (f : Z ⟶ X) (g : X ⟶ Y),
      e Y (f ≫ g) = G.map g (e X f))
    (R : InjectiveResolution F) (n : ℕ) :
    ↑((((CochainComplex.singleFunctor C 0).obj Z).HomComplex R.cochainComplex).homology n) ≃+
      ↑(((G.mapHomologicalComplex (.up ℤ)).obj R.cochainComplex).homology n) :=
  ((HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (.up ℤ) n).mapIso
    (RepresentedCochainSections.DerivedSections.homComplexIsoSections e he R.cochainComplex)).addCommGroupIsoToAddEquiv

lemma homComplexHomologyAddEquivSections_naturality
    (e : ∀ X : C, (Z ⟶ X) ≃+ ↑(G.obj X))
    (he : ∀ {X Y : C} (a : Z ⟶ X) (b : X ⟶ Y),
      e Y (a ≫ b) = G.map b (e X a))
    {F' : C} (R : InjectiveResolution F) (R' : InjectiveResolution F')
    (g : F ⟶ F') (φ : InjectiveResolution.Hom R R' g) (n : ℕ)
    (x : ↑((((CochainComplex.singleFunctor C 0).obj Z).HomComplex
      R.cochainComplex).homology n)) :
    homComplexHomologyAddEquivSections e he R' n
        (((HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (.up ℤ) n).map
          (RepresentedCochainNaturality.DerivedSections.homComplexPostcomp φ.hom')).hom x) =
      ((HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (.up ℤ) n).map
        ((G.mapHomologicalComplex (.up ℤ)).map φ.hom')).hom
          (homComplexHomologyAddEquivSections e he R n x) := by
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (.up ℤ) n
  have h := congrArg H.map (RepresentedCochainNaturality.DerivedSections.homComplexIsoSections_naturality e he φ.hom')
  rw [Functor.map_comp, Functor.map_comp] at h
  have hx := ConcreteCategory.congr_hom h x
  change (H.map (RepresentedCochainSections.DerivedSections.homComplexIsoSections e he R'.cochainComplex).hom).hom
      ((H.map (RepresentedCochainNaturality.DerivedSections.homComplexPostcomp φ.hom')).hom x) =
    (H.map ((G.mapHomologicalComplex (.up ℤ)).map φ.hom')).hom
      ((H.map (RepresentedCochainSections.DerivedSections.homComplexIsoSections e he R.cochainComplex).hom).hom x)
  exact hx

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ExtRepresentedHomology.DerivedSections
