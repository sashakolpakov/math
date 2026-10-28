import OAI.AlgebraicGeometry.ComplexMultiplication.MapStupidTrunc
import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.HypercohomologyPullback
import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.InverseImageMap

/-! # Filtered Pullback -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.FilteredPullback

noncomputable section

open scoped OAI.AlgebraicGeometry.Hodge.Filtration.ComplexPoint
open scoped OAI.AlgebraicGeometry.Hodge.HolomorphicDeRham.ComplexPoint

/-! # Pullback preserves the original geometric Hodge filtration

Actual scheme pullback acts on the original holomorphic de Rham complexes
and their truncations by form degree. The induced map preserves the original
image definition of the Hodge filtration in every degree.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry ComplexPoint

variable {X Y : Over (Spec (.of ℂ))}
  [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom]

/-- Actual inverse-image pullback on the original filtered de Rham complex. -/
def originalFilteredDeRhamInverseImagePullback (f : X ⟶ Y) (p : ℤ) :
    (AnalyticInverseImage.originalAnalyticInverseImageLocalizer f).functor.obj (F^p Ω•(Y)) ⟶ F^p Ω•(X) :=
  (MapStupidTrunc.HomologicalComplex.mapStupidTruncCanonicalIso (AnalyticInverseImage.originalAnalyticSheafInverseImage f)
    Ω•(Y) (ComplexShape.embeddingUpIntGE p)).hom ≫
      HomologicalComplex.stupidTruncMap (InverseImageMap.originalDeRhamInverseImagePullback f)
        (ComplexShape.embeddingUpIntGE p)

set_option backward.isDefEq.respectTransparency false in
/-- The filtered pullback retains the actual original inclusion into the de Rham complex. -/
theorem originalFilteredDeRhamInverseImagePullback_comp_inclusion (f : X ⟶ Y) (p : ℤ) :
    originalFilteredDeRhamInverseImagePullback f p ≫ ComplexPoint.Basic.ComplexSchemePoint.hodgeFilteredDeRhamInclusion X p =
      (AnalyticInverseImage.originalAnalyticInverseImageLocalizer f).functor.map
        (ComplexPoint.Basic.ComplexSchemePoint.hodgeFilteredDeRhamInclusion Y p) ≫ InverseImageMap.originalDeRhamInverseImagePullback f := by
  unfold originalFilteredDeRhamInverseImagePullback ComplexPoint.Basic.ComplexSchemePoint.hodgeFilteredDeRhamInclusion
  let b : ((AnalyticInverseImage.originalAnalyticSheafInverseImage f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      Ω•(Y) ⟶ Ω•(X) := InverseImageMap.originalDeRhamInverseImagePullback f
  change ((MapStupidTrunc.HomologicalComplex.mapStupidTruncCanonicalIso (AnalyticInverseImage.originalAnalyticSheafInverseImage f)
      Ω•(Y) (ComplexShape.embeddingUpIntGE p)).hom ≫
        HomologicalComplex.stupidTruncMap b (ComplexShape.embeddingUpIntGE p)) ≫
      Algebra.Homology.StupidTruncation.HomologicalComplex.stupidTruncInclusion Ω•(X) (ComplexShape.embeddingUpIntGE p) =
    ((AnalyticInverseImage.originalAnalyticSheafInverseImage f).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (Algebra.Homology.StupidTruncation.HomologicalComplex.stupidTruncInclusion Ω•(Y) (ComplexShape.embeddingUpIntGE p)) ≫ b
  rw [Category.assoc, Algebra.Homology.StupidTruncation.HomologicalComplex.stupidTruncMap_comp_stupidTruncInclusion,
    ← Category.assoc, MapStupidTrunc.HomologicalComplex.mapStupidTruncCanonicalIso_comp_inclusion]

/-- Genuine scheme pullback on the original de Rham hypercohomology. -/
def originalDeRhamHypercohomologyPullback (f : X ⟶ Y) (n : ℤ) :
    H_dR^n(Y) → H_dR^n(X) := fun α =>
  ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (InverseImageMap.originalDeRhamInverseImagePullback f) n
    (HypercohomologyPullback.originalHypercohomologyPullback f Ω•(Y) n α)

/-- Genuine scheme pullback on the original filtered de Rham hypercohomology. -/
def originalFilteredDeRhamHypercohomologyPullback (f : X ⟶ Y) (p n : ℤ) :
    ComplexPoint.Basic.ComplexSchemePoint.FilteredDeRhamHypercohomology Y p n → ComplexPoint.Basic.ComplexSchemePoint.FilteredDeRhamHypercohomology X p n := fun α =>
  ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (originalFilteredDeRhamInverseImagePullback f p) n
    (HypercohomologyPullback.originalHypercohomologyPullback f (F^p Ω•(Y)) n α)

/-- The map on filtered hypercohomology commutes with its original map to de Rham cohomology. -/
theorem originalDeRhamHypercohomologyPullback_filteredToDeRham (f : X ⟶ Y) (p n : ℤ)
    (α : ComplexPoint.Basic.ComplexSchemePoint.FilteredDeRhamHypercohomology Y p n) :
    originalDeRhamHypercohomologyPullback f n (ComplexPoint.Basic.ComplexSchemePoint.filteredToDeRhamCohomology Y p n α) =
      ComplexPoint.Basic.ComplexSchemePoint.filteredToDeRhamCohomology X p n
        (originalFilteredDeRhamHypercohomologyPullback f p n α) := by
  unfold originalDeRhamHypercohomologyPullback
    originalFilteredDeRhamHypercohomologyPullback ComplexPoint.Basic.ComplexSchemePoint.filteredToDeRhamCohomology
  rw [HypercohomologyPullback.originalHypercohomologyPullback_naturality,
    ← ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap_comp_apply, ← ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap_comp_apply,
    originalFilteredDeRhamInverseImagePullback_comp_inclusion]

/-- Pullback of actual scheme maps preserves the original geometric Hodge filtration. -/
theorem originalDeRhamHypercohomologyPullback_mem_hodgeFiltration (f : X ⟶ Y)
    (p n : ℤ) {α : H_dR^n(Y)} (hα : α ∈ ComplexPoint.Basic.ComplexSchemePoint.hodgeFiltration Y p n) :
    originalDeRhamHypercohomologyPullback f n α ∈ ComplexPoint.Basic.ComplexSchemePoint.hodgeFiltration X p n := by
  rcases hα with ⟨β, rfl⟩
  exact ⟨originalFilteredDeRhamHypercohomologyPullback f p n β,
    (originalDeRhamHypercohomologyPullback_filteredToDeRham f p n β).symm⟩

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.FilteredPullback
