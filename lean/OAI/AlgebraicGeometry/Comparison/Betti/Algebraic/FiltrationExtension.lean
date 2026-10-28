import OAI.AlgebraicGeometry.Comparison.Betti.NonnegativeExtensionNaturality
import OAI.AlgebraicGeometry.Comparison.Betti.Analytic.De
import OAI.NumberTheory.PadicHodge.GeometricComparison.FilteredComplexAdapter

/-! # Filtration Extension -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.FiltrationExtension

noncomputable section

section

/-! BettiComparison's independent algebraic filtration uses the same preserved sheaf-extension comparison under the two canonical indexing conventions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)

theorem algebraicSheafIntExtensionIso_adapter :
    NumberTheory.PadicHodge.GeometricComparison.SheafFormsAdapter.FormsAdapter.sheafIntExtensionIso X = Analytic.De.algebraicSheafIntExtensionIso X ≪≫
      NonnegativeExtensionNormalization.Complex.nonnegativeExtensionIso (Sheaves.algebraicDeRhamSheafComplex X) := rfl

def algebraicTruncationComplexInt (r : ℤ) : CochainComplex (Sheaves.ComplexSheaves X) ℤ :=
  (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal (Sheaves.algebraicDeRhamSheafComplex X) r).extend (ComplexShape.embeddingUpIntGE 0)

def algebraicTruncationInclusionInt (r : ℤ) : algebraicTruncationComplexInt X r ⟶
    Sheaves.algebraicDeRhamSheafComplexInt X :=
  HomologicalComplex.extendMap (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion (Sheaves.algebraicDeRhamSheafComplex X) r) (ComplexShape.embeddingUpIntGE 0) ≫
    (Analytic.De.algebraicSheafIntExtensionIso X).inv

theorem algebraicTruncationInclusionInt_adapter (r : ℤ) :
    (NonnegativeExtensionNormalization.Complex.nonnegativeExtensionIso (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal (Sheaves.algebraicDeRhamSheafComplex X) r)).hom ≫
      HomologicalComplex.extendMap (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion (Sheaves.algebraicDeRhamSheafComplex X) r) ComplexShape.embeddingUpNat ≫
        (NumberTheory.PadicHodge.GeometricComparison.SheafFormsAdapter.FormsAdapter.sheafIntExtensionIso X).inv = algebraicTruncationInclusionInt X r := by
  rw [algebraicSheafIntExtensionIso_adapter]
  change _ ≫ _ ≫ ((NonnegativeExtensionNormalization.Complex.nonnegativeExtensionIso (Sheaves.algebraicDeRhamSheafComplex X)).inv ≫
    (Analytic.De.algebraicSheafIntExtensionIso X).inv) = _
  rw [← Category.assoc, NonnegativeExtensionNaturality.Complex.nonnegativeExtensionIso_naturality]
  erw [Category.assoc, Iso.hom_inv_id_assoc]
  rfl

end

/-! The exact independent algebraic Hodge filtration is the image of its original truncation inclusion under canonical integer extension. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (n : ℕ) (r : ℤ)

abbrev algebraicTruncatedCohomology :=
  (DerivedCategory.singleFunctor (Sheaves.ComplexSheaves X) 0).obj (Sheaves.constantComplexSheaf X) ⟶
    (DerivedCategory.Q.obj (algebraicTruncationComplexInt X r))⟦(n : ℤ)⟧

def algebraicTruncationClass : algebraicTruncatedCohomology X n r →ₗ[ℂ] Sheaves.algebraicDeRham X n :=
  Linear.rightComp ℂ _ ((DerivedCategory.Q.map (algebraicTruncationInclusionInt X r))⟦(n : ℤ)⟧')

def algebraicTruncationAdapterEquiv : algebraicTruncatedCohomology X n r ≃ₗ[ℂ]
    NumberTheory.PadicHodge.GeometricComparison.FilteredComplexAdapter.FormsAdapter.NatCohomology X (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal (Sheaves.algebraicDeRhamSheafComplex X) r) n :=
  Linear.homCongr ℂ (Iso.refl _)
    ((shiftFunctor (DerivedCategory (Sheaves.ComplexSheaves X)) (n : ℤ)).mapIso
      (DerivedCategory.Q.mapIso
        (NonnegativeExtensionNormalization.Complex.nonnegativeExtensionIso (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal (Sheaves.algebraicDeRhamSheafComplex X) r))))

theorem filtrationMap66_normalized (a : algebraicTruncatedCohomology X n r) :
    NumberTheory.PadicHodge.GeometricComparison.FilteredComplexAdapter.FormsAdapter.filtrationMap66 X n r (algebraicTruncationAdapterEquiv X n r a) =
      algebraicTruncationClass X n r a := by
  let Q := DerivedCategory.Q (C := Sheaves.ComplexSheaves X)
  let S := shiftFunctor (DerivedCategory (Sheaves.ComplexSheaves X)) (n : ℤ)
  let u := (NonnegativeExtensionNormalization.Complex.nonnegativeExtensionIso (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal (Sheaves.algebraicDeRhamSheafComplex X) r)).hom
  let v := HomologicalComplex.extendMap (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion (Sheaves.algebraicDeRhamSheafComplex X) r) ComplexShape.embeddingUpNat
  let w := (NumberTheory.PadicHodge.GeometricComparison.SheafFormsAdapter.FormsAdapter.sheafIntExtensionIso X).inv
  have hu : u ≫ v ≫ w = algebraicTruncationInclusionInt X r := algebraicTruncationInclusionInt_adapter X r
  have hQ : Q.map u ≫ Q.map v ≫ Q.map w = Q.map (algebraicTruncationInclusionInt X r) :=
    (congrArg (Q.map u ≫ ·) (Q.map_comp v w).symm).trans
      ((Q.map_comp u (v ≫ w)).symm.trans (congrArg Q.map hu))
  have hS : S.map (Q.map u) ≫ S.map (Q.map v ≫ Q.map w) =
      S.map (Q.map (algebraicTruncationInclusionInt X r)) :=
    (S.map_comp (Q.map u) (Q.map v ≫ Q.map w)).symm.trans (congrArg S.map hQ)
  change ((𝟙 _ ≫ a) ≫ S.map (Q.map u)) ≫ S.map (Q.map v ≫ Q.map w) =
    a ≫ S.map (Q.map (algebraicTruncationInclusionInt X r))
  rw [Category.id_comp]
  exact (Category.assoc _ _ _).trans (congrArg (a ≫ ·) hS)

theorem filtration66_mem_iff_truncatedClass (a : Sheaves.algebraicDeRham X n) :
    a ∈ NumberTheory.PadicHodge.GeometricComparison.FilteredComplexAdapter.FormsAdapter.filtration66 X n r ↔
      ∃ b : algebraicTruncatedCohomology X n r, algebraicTruncationClass X n r b = a := by
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨(algebraicTruncationAdapterEquiv X n r).symm b, ?_⟩
    have h := filtrationMap66_normalized X n r ((algebraicTruncationAdapterEquiv X n r).symm b)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm.trans hb
  · rintro ⟨b, hb⟩
    exact ⟨algebraicTruncationAdapterEquiv X n r b, (filtrationMap66_normalized X n r b).trans hb⟩

end

end OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.FiltrationExtension
