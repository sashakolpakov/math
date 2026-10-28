import OAI.NumberTheory.PadicHodge.GeometricComparison.SheafFormsAdapter
import OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.Int
import OAI.AlgebraicGeometry.Comparison.Betti.OpenForms

/-! # Sheaf Adapter Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.SheafAdapterNaturality.FormsAdapter

noncomputable section

/-! Pullback compatibility for the actual algebraic form and sheaf comparisons. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem composition_square {C : Type*} [Category* C] {A B C' D E F : C}
    {a : A ⟶ B} {b : B ⟶ C'} {c : A ⟶ D} {d : D ⟶ C'}
    {e : C' ⟶ F} {f : D ⟶ E} {g : E ⟶ F}
    (h₁ : a ≫ b = c ≫ d) (h₂ : d ≫ e = f ≫ g) :
    a ≫ (b ≫ e) = (c ≫ f) ≫ g := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc]

variable {X Y : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y)

theorem presheafComplexIso_naturality :
    (SheafFormsAdapter.FormsAdapter.presheafComplexIso Y).hom ≫ DeRham.Int.presheafPullback f =
      AlgebraicGeometry.Comparison.Betti.Sheaf.CochainPullback.presheafComplexPullback f ≫
        ((DeRham.Int.directImagePresheaf f).mapHomologicalComplex (ComplexShape.up ℕ)).map
          (SheafFormsAdapter.FormsAdapter.presheafComplexIso X).hom := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ω
  exact (Forms.Adapter.FormsAdapter.to62_pullback Γ(Y.left, U.unop) (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.sectionPullback f U.unop) n ω).symm

theorem presheafSheafUnit_naturality :
    (SheafFormsAdapter.FormsAdapter.presheafComplexIso Y).hom ≫ DeRham.Int.presheafToDirectImageSheafComplex f =
      AlgebraicGeometry.Comparison.Betti.Sheaf.CochainPullback.presheafToDirectImageSheafComplex f ≫
        ((sheafToPresheaf (Opens.grothendieckTopology Y.left) (ModuleCat.{0} ℂ)).mapHomologicalComplex
          (ComplexShape.up ℕ)).map
          (((DeRham.Int.directImage f).mapHomologicalComplex (ComplexShape.up ℕ)).map
            (SheafFormsAdapter.FormsAdapter.sheafComplexIso X).hom) := by
  let D := (DeRham.Int.directImagePresheaf f).mapHomologicalComplex (ComplexShape.up ℕ)
  have hunit := (DeRham.Int.sheafificationComplexAdjunction X).unit.naturality
    (SheafFormsAdapter.FormsAdapter.presheafComplexIso X).hom
  have h := congrArg (fun k => D.map k) hunit
  change D.map ((SheafFormsAdapter.FormsAdapter.presheafComplexIso X).hom ≫
      (DeRham.Int.sheafificationComplexAdjunction X).unit.app (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex ℂ X)) =
    D.map ((DeRham.Int.sheafificationComplexAdjunction X).unit.app (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.deRhamPresheafComplex X) ≫
      ((sheafToPresheaf (Opens.grothendieckTopology X.left) (ModuleCat.{0} ℂ)).mapHomologicalComplex
        (ComplexShape.up ℕ)).map (SheafFormsAdapter.FormsAdapter.sheafComplexIso X).hom) at h
  simp only [Functor.map_comp] at h
  change (SheafFormsAdapter.FormsAdapter.presheafComplexIso Y).hom ≫
      (DeRham.Int.presheafPullback f ≫ D.map
        ((DeRham.Int.sheafificationComplexAdjunction X).unit.app (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex ℂ X))) =
    (AlgebraicGeometry.Comparison.Betti.Sheaf.CochainPullback.presheafComplexPullback f ≫ D.map
      ((DeRham.Int.sheafificationComplexAdjunction X).unit.app (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.deRhamPresheafComplex X))) ≫
      D.map (((sheafToPresheaf (Opens.grothendieckTopology X.left) (ModuleCat.{0} ℂ)).mapHomologicalComplex
        (ComplexShape.up ℕ)).map (SheafFormsAdapter.FormsAdapter.sheafComplexIso X).hom)
  exact composition_square (presheafComplexIso_naturality f) h

theorem sheafComplexIso_direct_naturality :
    (SheafFormsAdapter.FormsAdapter.sheafComplexIso Y).hom ≫ DeRham.Int.sheafDirectImage f =
      AlgebraicGeometry.Comparison.Betti.Sheaf.CochainPullback.deRhamSheafDirectImage f ≫
        ((DeRham.Int.directImage f).mapHomologicalComplex (ComplexShape.up ℕ)).map
          (SheafFormsAdapter.FormsAdapter.sheafComplexIso X).hom :=
  (DeRham.Int.sheafificationComplexAdjunction Y).homEquiv_naturality_right_square
    (SheafFormsAdapter.FormsAdapter.presheafComplexIso Y).hom (DeRham.Int.presheafToDirectImageSheafComplex f)
    (AlgebraicGeometry.Comparison.Betti.Sheaf.CochainPullback.presheafToDirectImageSheafComplex f)
    (((DeRham.Int.directImage f).mapHomologicalComplex (ComplexShape.up ℕ)).map
      (SheafFormsAdapter.FormsAdapter.sheafComplexIso X).hom) (presheafSheafUnit_naturality f)

theorem sheafComplexIso_naturality :
    ((DeRham.Int.inverseImage f).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (SheafFormsAdapter.FormsAdapter.sheafComplexIso Y).hom ≫ DeRham.Int.sheafPullback f =
      AlgebraicGeometry.Comparison.Betti.Sheaf.CochainPullback.deRhamSheafPullback f ≫ (SheafFormsAdapter.FormsAdapter.sheafComplexIso X).hom :=
  (DeRham.Int.imageComplexAdjunction f).homEquiv_naturality_right_square
    (SheafFormsAdapter.FormsAdapter.sheafComplexIso Y).hom (DeRham.Int.sheafDirectImage f)
    (AlgebraicGeometry.Comparison.Betti.Sheaf.CochainPullback.deRhamSheafDirectImage f) (SheafFormsAdapter.FormsAdapter.sheafComplexIso X).hom
    (sheafComplexIso_direct_naturality f)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.SheafAdapterNaturality.FormsAdapter
