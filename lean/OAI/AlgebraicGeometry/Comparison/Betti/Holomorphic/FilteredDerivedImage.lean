import OAI.AlgebraicGeometry.Comparison.Betti.Filtered.DerivedInclusion
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.FilteredQuasiIso

/-! # Filtered Derived Image -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.FilteredDerivedImage.Hodge

noncomputable section

/-! The image of the original holomorphic degree truncation in smooth
hypercohomology is exactly the classes of actual closed filtered smooth forms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

local instance : HasDerivedCategory.{1} (ConstantSheafSections.ComplexSheaves (TopCat.of M)) := HasDerivedCategory.standard _

abbrev holomorphicTruncatedComplexNat (r : ℤ) :
    CochainComplex (ConstantSheafSections.ComplexSheaves (TopCat.of M)) ℕ :=
  Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal (SheafComplex.sheafComplex E M) r

def holomorphicTruncationToSmoothDerived (r : ℤ) :
    DerivedCategory.Q.obj ((holomorphicTruncatedComplexNat E M r).extend (ComplexShape.embeddingUpIntGE 0)) ⟶
      DerivedCategory.Q.obj ((Filtered.DerivedInclusion.Hodge.smoothSheafComplexNat E M).extend (ComplexShape.embeddingUpIntGE 0)) :=
  DerivedCategory.Q.map (HomologicalComplex.extendMap
    (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion (SheafComplex.sheafComplex E M) r ≫ SheafComplex.inclusionSheafMap E M)
    (ComplexShape.embeddingUpIntGE 0))

def filteredSmoothToSmoothDerived (r : ℤ) :
    DerivedCategory.Q.obj ((Filtered.DerivedRepresentatives.Hodge.filteredSheafComplexNat E M r).extend (ComplexShape.embeddingUpIntGE 0)) ⟶
      DerivedCategory.Q.obj ((Filtered.DerivedInclusion.Hodge.smoothSheafComplexNat E M).extend (ComplexShape.embeddingUpIntGE 0)) :=
  DerivedCategory.Q.map (HomologicalComplex.extendMap (Filtered.SmoothComplex.Hodge.filteredSmoothSheafInclusion E M r)
    (ComplexShape.embeddingUpIntGE 0))

def holomorphicTruncationToFilteredDerivedIso (r : ℤ) :
    DerivedCategory.Q.obj ((holomorphicTruncatedComplexNat E M r).extend (ComplexShape.embeddingUpIntGE 0)) ≅
      DerivedCategory.Q.obj ((Filtered.DerivedRepresentatives.Hodge.filteredSheafComplexNat E M r).extend (ComplexShape.embeddingUpIntGE 0)) := by
  let f : (holomorphicTruncatedComplexNat E M r).extend (ComplexShape.embeddingUpIntGE 0) ⟶
      (Filtered.DerivedRepresentatives.Hodge.filteredSheafComplexNat E M r).extend (ComplexShape.embeddingUpIntGE 0) :=
    HomologicalComplex.extendMap (FilteredComplex.Hodge.holomorphicFilteredSheafMap E M r) (ComplexShape.embeddingUpIntGE 0)
  have hf : QuasiIso f := (HomologicalComplex.quasiIso_extendMap_iff
    (FilteredComplex.Hodge.holomorphicFilteredSheafMap E M r) (ComplexShape.embeddingUpIntGE 0)).mpr
      (FilteredQuasiIso.Hodge.holomorphicFilteredSheafMap_quasiIso E M r)
  have : IsIso (DerivedCategory.Q.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (ConstantSheafSections.ComplexSheaves (TopCat.of M)) f).mpr hf
  exact asIso (DerivedCategory.Q.map f)

theorem holomorphicTruncationDerived_factorization (r : ℤ) :
    (holomorphicTruncationToFilteredDerivedIso E M r).hom ≫ filteredSmoothToSmoothDerived E M r =
      holomorphicTruncationToSmoothDerived E M r := by
  change DerivedCategory.Q.map (HomologicalComplex.extendMap (FilteredComplex.Hodge.holomorphicFilteredSheafMap E M r)
      (ComplexShape.embeddingUpIntGE 0)) ≫
    DerivedCategory.Q.map (HomologicalComplex.extendMap (Filtered.SmoothComplex.Hodge.filteredSmoothSheafInclusion E M r)
      (ComplexShape.embeddingUpIntGE 0)) = _
  erw [← CategoryTheory.Functor.map_comp, ← HomologicalComplex.extendMap_comp,
    FilteredComplex.Hodge.holomorphicFilteredSheafMap_factorization]
  rfl

variable [CompactSpace M] [T2Space M]

theorem holomorphicTruncation_image_iff_closed_filtered (n : ℕ) (r : ℤ)
    (a : (DerivedCategory.singleFunctor (ConstantSheafSections.ComplexSheaves (TopCat.of M)) 0).obj
        (ConstantSheafSections.standardConstantSheaf (TopCat.of M)) ⟶
      (DerivedCategory.Q.obj ((Filtered.DerivedInclusion.Hodge.smoothSheafComplexNat E M).extend
        (ComplexShape.embeddingUpIntGE 0)))⟦(n : ℤ)⟧) :
    (∃ c : (DerivedCategory.singleFunctor (ConstantSheafSections.ComplexSheaves (TopCat.of M)) 0).obj
        (ConstantSheafSections.standardConstantSheaf (TopCat.of M)) ⟶
      (DerivedCategory.Q.obj ((holomorphicTruncatedComplexNat E M r).extend
        (ComplexShape.embeddingUpIntGE 0)))⟦(n : ℤ)⟧,
      c ≫ (holomorphicTruncationToSmoothDerived E M r)⟦(n : ℤ)⟧' = a) ↔
    ∃ (b : ManifoldFormFiltration.Hodge.manifoldFormFiltration E M n r) (hb : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d b.val = 0),
      Filtered.DerivedInclusion.Hodge.smoothGlobalDerivedClass E M n b.val hb = a := by
  let e := (shiftFunctor (DerivedCategory (ConstantSheafSections.ComplexSheaves (TopCat.of M))) (n : ℤ)).mapIso
    (holomorphicTruncationToFilteredDerivedIso E M r)
  have hw : (holomorphicTruncationToSmoothDerived E M r)⟦(n : ℤ)⟧' =
      e.hom ≫ (filteredSmoothToSmoothDerived E M r)⟦(n : ℤ)⟧' := by
    rw [← holomorphicTruncationDerived_factorization, CategoryTheory.Functor.map_comp]
    rfl
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨b, hb, hbc⟩ := Filtered.DerivedRepresentatives.Hodge.exists_filtered_global_derived_representative E M n r (c ≫ e.hom)
    refine ⟨b, hb, ?_⟩
    rw [← Filtered.DerivedInclusion.Hodge.filteredGlobalDerivedClass_inclusion E M n r b hb, hbc]
    rw [hw, ← Category.assoc] at hc
    exact hc
  · rintro ⟨b, hb, hba⟩
    refine ⟨Filtered.DerivedRepresentatives.Hodge.filteredGlobalDerivedClass E M n r b hb ≫ e.inv, ?_⟩
    rw [hw, Category.assoc, e.inv_hom_id_assoc]
    exact (Filtered.DerivedInclusion.Hodge.filteredGlobalDerivedClass_inclusion E M n r b hb).trans hba

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.FilteredDerivedImage.Hodge
