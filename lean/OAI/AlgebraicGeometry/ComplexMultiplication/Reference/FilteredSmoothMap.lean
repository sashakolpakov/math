import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.FilteredSmoothInt
import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.FilteredSmoothSheafMap
import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.FilteredGlobalClasses
import OAI.AlgebraicGeometry.ComplexMultiplication.MonicFactor

/-! # Filtered Smooth Map -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.FilteredSmoothMap

noncomputable section

open scoped OAI.AlgebraicGeometry.Hodge.Filtration.ComplexPoint
open scoped OAI.AlgebraicGeometry.Hodge.HolomorphicDeRham.ComplexPoint

section

/-! # The original holomorphic filtration maps to actual filtered smooth forms

The composite with the genuine filtered inclusion is exactly the original
holomorphic-to-smooth map. The differential is consequently unchanged.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

attribute [reassoc] FilteredSmoothSheafMap.originalHolomorphicToFilteredSmoothSheaf_comp_inclusion

attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace
attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

/-- The component is actual holomorphic-form evaluation in retained degrees, and zero elsewhere. -/
def originalFilteredHolomorphicSmoothComponent (p : ℕ) (n : ℤ) :
    (F^(p : ℤ) Ω•(X)).X n ⟶ (FilteredSmoothInt.originalFilteredSmoothComplexInt X p).X n :=
  match n with
  | .ofNat q =>
    if hp : p ≤ q then
      (ComplexPoint.Basic.ComplexSchemePoint.hodgeFilteredDeRhamInclusion X p).f (q : ℤ) ≫
        ((ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamComplex X (Topology.Dimension.Basic.TopologicalSpace.dim X.left)).extendXIso
          ComplexShape.embeddingUpNat (i := q) rfl).hom ≫
            FilteredSmoothSheafMap.originalHolomorphicToFilteredSmoothSheaf X q p (by exact_mod_cast hp) ≫
              ((FilteredSmoothAdditiveAcyclic.originalFilteredSmoothComplexNat X p).extendXIso
                ComplexShape.embeddingUpNat (i := q) rfl).inv
    else 0
  | .negSucc _ => 0

set_option backward.isDefEq.respectTransparency false in
/-- These factors recover every component of the unchanged original chain map. -/
theorem originalFilteredHolomorphicSmoothComponent_comp (p : ℕ) (n : ℤ) :
    originalFilteredHolomorphicSmoothComponent X p n ≫
        (FilteredSmoothInt.originalFilteredSmoothInclusionInt X p).f n =
      (ComplexPoint.Basic.ComplexSchemePoint.hodgeFilteredDeRhamInclusion X p ≫ ReferenceSmooth.Hypercohomology.originalHolomorphicToSmoothSheafComplexInt X).f n := by
  let : (F^(p : ℤ) Ω•(X)).IsStrictlyGE p := FilteredGlobalClasses.originalFilteredDeRham_isStrictlyGE X p
  cases n with
  | ofNat q =>
    change originalFilteredHolomorphicSmoothComponent X p (q : ℤ) ≫ _ = _
    dsimp only [originalFilteredHolomorphicSmoothComponent]
    split_ifs with hp
    · change (_ ≫ _ ≫ _ ≫ _) ≫
        (HomologicalComplex.extendMap (FilteredSmoothAdditiveAcyclic.originalFilteredSmoothInclusionNat X p)
          ComplexShape.embeddingUpNat).f (q : ℤ) =
        (ComplexPoint.Basic.ComplexSchemePoint.hodgeFilteredDeRhamInclusion X p).f (q : ℤ) ≫
          (HomologicalComplex.extendMap (ReferenceSmooth.FormSheaf.originalHolomorphicToSmoothSheafComplex X)
            ComplexShape.embeddingUpNat).f (q : ℤ)
      rw [HomologicalComplex.extendMap_f _ _ (i := q) (i' := (q : ℤ)) rfl,
        HomologicalComplex.extendMap_f _ _ (i := q) (i' := (q : ℤ)) rfl]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      change _ ≫ _ ≫ (FilteredSmoothSheafMap.originalHolomorphicToFilteredSmoothSheaf X q p _) ≫
        (ReferenceSmooth.FormSheaf.originalSmoothFormSheafForget X).map
          (Comparison.Betti.Filtered.SmoothComplex.Hodge.filteredFormSheafInclusion (Fin (Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ)
            (ComplexPoint.Basic.ComplexSchemePoint X) q p) ≫ _ = _
      rw [FilteredSmoothSheafMap.originalHolomorphicToFilteredSmoothSheaf_comp_inclusion_assoc]
      rfl
    · exact (CochainComplex.isZero_of_isStrictlyGE (F^(p : ℤ) Ω•(X)) p (q : ℤ)
        (by exact_mod_cast Nat.lt_of_not_ge hp)).eq_of_src _ _
  | negSucc q =>
    exact (CochainComplex.isZero_of_isStrictlyGE (F^(p : ℤ) Ω•(X)) p (Int.negSucc q)
      (by omega)).eq_of_src _ _

/-- The literal original filtered complex maps into the actual smooth filtration. -/
def originalFilteredHolomorphicToSmoothComplex (p : ℕ) :
    F^(p : ℤ) Ω•(X) ⟶ FilteredSmoothInt.originalFilteredSmoothComplexInt X p :=
  MonicFactor.complexMonicFactor (FilteredSmoothInt.originalFilteredSmoothInclusionInt X p)
    (ComplexPoint.Basic.ComplexSchemePoint.hodgeFilteredDeRhamInclusion X p ≫ ReferenceSmooth.Hypercohomology.originalHolomorphicToSmoothSheafComplexInt X)
    (originalFilteredHolomorphicSmoothComponent X p)
    (originalFilteredHolomorphicSmoothComponent_comp X p)

/-- Its composite retains the complete original de Rham comparison map. -/
theorem originalFilteredHolomorphicToSmoothComplex_comp_inclusion (p : ℕ) :
    originalFilteredHolomorphicToSmoothComplex X p ≫
        FilteredSmoothInt.originalFilteredSmoothInclusionInt X p =
      ComplexPoint.Basic.ComplexSchemePoint.hodgeFilteredDeRhamInclusion X p ≫ ReferenceSmooth.Hypercohomology.originalHolomorphicToSmoothSheafComplexInt X :=
  MonicFactor.complexMonicFactor_comp _ _ _ _

end

/-! # Every original filtered class has an actual filtered smooth representative -/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint

attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace
attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom] [Foundations.ProjectiveSpaceIs.IsProjective X.hom]

local notation "ΓInt" => Functor.mapHomologicalComplex
  (AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
    (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) (ComplexShape.up ℤ)

/-- The representative maps through the unchanged original comparison and genuine inclusion. -/
theorem originalHodgeFiltration_filteredSmoothRepresentative (p : ℕ) (n : ℤ)
    (α : H_dR^n(X)) (hα : α ∈ ComplexPoint.Basic.ComplexSchemePoint.hodgeFiltration X p n) :
    ∃ z : (Cohomology.GlobalSections.TopCat.Sheaf.globalSectionsComplexInt (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
      (FilteredSmoothInt.originalFilteredSmoothComplexInt X p)).homology n,
      ReferenceSmooth.Hypercohomology.originalDeRhamSmoothHypercohomologyAddEquiv X n α =
        GlobalNaturality.globalSectionsToHypercohomology X (ReferenceSmooth.Integration.originalSmoothDeRhamComplexInt X) n
          (HomologicalComplex.homologyMap ((ΓInt).map
            (FilteredSmoothInt.originalFilteredSmoothInclusionInt X p)) n z) := by
  rcases hα with ⟨β, rfl⟩
  obtain ⟨z, hz⟩ := FilteredSmoothInt.originalFilteredSmoothGlobalClass_surjective X (p : ℤ) n
    (ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (originalFilteredHolomorphicToSmoothComplex X p) n β)
  refine ⟨z, ?_⟩
  rw [GlobalNaturality.globalSectionsToHypercohomology_naturality, hz,
    ← ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap_comp_apply,
    originalFilteredHolomorphicToSmoothComplex_comp_inclusion,
    ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap_comp_apply]
  rfl

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.FilteredSmoothMap
