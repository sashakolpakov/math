import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.ExtensionAdapter
import OAI.NumberTheory.PadicHodge.GeometricComparison.FilteredComplexAdapter

/-! # Adapter Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.AdapterNaturality.FormsAdapter

noncomputable section

/-! Functoriality of the filtered comparison between BettiComparison and Cohomology de Rham cohomology. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem map_commuting_square {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {A B C' D' : C} {a : A ⟶ B} {b : B ⟶ D'} {c : A ⟶ C'} {d : C' ⟶ D'}
    (h : a ≫ b = c ≫ d) : F.map a ≫ F.map b = F.map c ≫ F.map d :=
  (F.map_comp a b).symm.trans ((congrArg (fun t => F.map t) h).trans (F.map_comp c d))

variable {X Y : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y)

theorem derivedComparison_naturality :
    (Int.derivedInverseImage f).map (DerivedCategory.Q.map (SheafFormsAdapter.FormsAdapter.sheafComplexIntIso Y).hom) ≫
        Int.derivedPullback f =
      AlgebraicGeometry.Comparison.Betti.OpenForms.derivedDeRhamPullback f ≫ DerivedCategory.Q.map (SheafFormsAdapter.FormsAdapter.sheafComplexIntIso X).hom := by
  have h := (Int.inverseImage f).mapDerivedCategoryFactors.hom.naturality
    (SheafFormsAdapter.FormsAdapter.sheafComplexIntIso Y).hom
  change (Int.derivedInverseImage f).map (DerivedCategory.Q.map (SheafFormsAdapter.FormsAdapter.sheafComplexIntIso Y).hom) ≫
      (Int.inverseImage f).mapDerivedCategoryFactors.hom.app (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplexInt ℂ Y) =
    (Int.inverseImage f).mapDerivedCategoryFactors.hom.app (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.algebraicDeRhamSheafComplexInt Y) ≫
      DerivedCategory.Q.map
        (((Int.inverseImage f).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (SheafFormsAdapter.FormsAdapter.sheafComplexIntIso Y).hom) at h
  have h₂ := map_commuting_square DerivedCategory.Q (Intrinsic.ExtensionAdapter.FormsAdapter.sheafComplexIntIso_naturality f)
  exact SheafAdapterNaturality.FormsAdapter.composition_square h h₂

theorem cohomologyEquiv_apply (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) (n : ℕ) (a : AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.algebraicDeRham X n) :
    SheafFormsAdapter.FormsAdapter.cohomologyEquiv X n a = a ≫
      (shiftFunctor (DerivedCategory (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.ComplexSheaves X)) (n : ℤ)).map
        (DerivedCategory.Q.map (SheafFormsAdapter.FormsAdapter.sheafComplexIntIso X).hom) := by
  change (𝟙 _ ≫ a) ≫ _ = a ≫ _
  exact congrArg (fun t => t ≫ _) (Category.id_comp a)

/-- Compatibility with the independently constructed native cohomological pullbacks. -/
theorem cohomologyEquiv_pullback (n : ℕ) (a : AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.algebraicDeRham Y n) :
    SheafFormsAdapter.FormsAdapter.cohomologyEquiv X n ((AlgebraicGeometry.Comparison.Betti.OpenForms.algebraicDeRhamPullback f n).hom a) =
      Int.pullback f n (SheafFormsAdapter.FormsAdapter.cohomologyEquiv Y n a) := by
  change (DerivedCategory.singleFunctor (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.ComplexSheaves Y) 0).obj
    (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.constantComplexSheaf Y) ⟶
      (DerivedCategory.Q.obj (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.algebraicDeRhamSheafComplexInt Y))⟦(n : ℤ)⟧ at a
  erw [cohomologyEquiv_apply, cohomologyEquiv_apply]
  let S := shiftFunctor (DerivedCategory (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.ComplexSheaves X)) (n : ℤ)
  have hshift := ((AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.derivedInverseImage f).commShiftIso (n : ℤ)).hom.naturality
    (DerivedCategory.Q.map (SheafFormsAdapter.FormsAdapter.sheafComplexIntIso Y).hom)
  change (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.derivedInverseImage f).map
      ((shiftFunctor (DerivedCategory (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.ComplexSheaves Y)) (n : ℤ)).map
        (DerivedCategory.Q.map (SheafFormsAdapter.FormsAdapter.sheafComplexIntIso Y).hom)) ≫
      ((AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.derivedInverseImage f).commShiftIso (n : ℤ)).hom.app
        (DerivedCategory.Q.obj (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplexInt ℂ Y)) =
    ((AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.derivedInverseImage f).commShiftIso (n : ℤ)).hom.app
        (DerivedCategory.Q.obj (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.algebraicDeRhamSheafComplexInt Y)) ≫
      S.map ((AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.derivedInverseImage f).map
        (DerivedCategory.Q.map (SheafFormsAdapter.FormsAdapter.sheafComplexIntIso Y).hom)) at hshift
  change ((AlgebraicGeometry.Comparison.Betti.OpenForms.derivedInverseImageConstantIso f).inv ≫ (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.derivedInverseImage f).map a ≫
      ((AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.derivedInverseImage f).commShiftIso (n : ℤ)).hom.app
        (DerivedCategory.Q.obj (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.algebraicDeRhamSheafComplexInt Y)) ≫
      S.map (AlgebraicGeometry.Comparison.Betti.OpenForms.derivedDeRhamPullback f)) ≫
      S.map (DerivedCategory.Q.map (SheafFormsAdapter.FormsAdapter.sheafComplexIntIso X).hom) =
    (AlgebraicGeometry.Comparison.Betti.OpenForms.derivedInverseImageConstantIso f).inv ≫
      (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.derivedInverseImage f).map (a ≫
        (shiftFunctor (DerivedCategory (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.ComplexSheaves Y)) (n : ℤ)).map
          (DerivedCategory.Q.map (SheafFormsAdapter.FormsAdapter.sheafComplexIntIso Y).hom)) ≫
      ((AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.derivedInverseImage f).commShiftIso (n : ℤ)).hom.app
        (DerivedCategory.Q.obj (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplexInt ℂ Y)) ≫ S.map (Int.derivedPullback f)
  erw [(AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.derivedInverseImage f).map_comp]
  simp only [Category.assoc]
  have hnat : (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.derivedInverseImage f).map
      (DerivedCategory.Q.map (SheafFormsAdapter.FormsAdapter.sheafComplexIntIso Y).hom) ≫ Int.derivedPullback f =
    AlgebraicGeometry.Comparison.Betti.OpenForms.derivedDeRhamPullback f ≫ DerivedCategory.Q.map (SheafFormsAdapter.FormsAdapter.sheafComplexIntIso X).hom :=
    derivedComparison_naturality f
  have hmap := map_commuting_square S hnat
  have ht := (SheafAdapterNaturality.FormsAdapter.composition_square hshift hmap).trans (Category.assoc _ _ _)
  exact congrArg (fun k => (AlgebraicGeometry.Comparison.Betti.OpenForms.derivedInverseImageConstantIso f).inv ≫
    (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.derivedInverseImage f).map a ≫ k) ht.symm

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.AdapterNaturality.FormsAdapter
