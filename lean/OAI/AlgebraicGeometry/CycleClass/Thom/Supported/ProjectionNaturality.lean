import OAI.AlgebraicGeometry.CycleClass.Thom.CompactFiberSlant

/-! # Projection Naturality -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionNaturality.Constructions

noncomputable section

/-! Supported projection commutes with actual base maps, including transverse slices. -/

open _root_.CategoryTheory _root_.HomologicalComplex
open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels
open scoped _root_.Manifold

open OAI.AlgebraicGeometry.CycleClass.Thom.CompactFiberSlant.Constructions.SupportedProjection OAI.AlgebraicGeometry.CycleClass.Thom.CompactFiberSlant.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Relative.SlantNaturality.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem projectSupported_natural (d : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M]
    {X Y : TopCat.{0}} (f : X ⟶ Y) (S : Set X) (S' : Set Y)
    (T : Set (X × M)) (T' : Set (Y × M)) (K : Set M) (hK : IsCompact K)
    (hT : T ⊆ S ×ˢ K) (hT' : T' ⊆ S' ×ˢ K) (hf : Set.MapsTo f Sᶜ S'ᶜ)
    (hF : Set.MapsTo
      (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((f, 𝟙 (TopCat.of M)) : (X, TopCat.of M) ⟶ (Y, TopCat.of M))) Tᶜ T'ᶜ)
    (p : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (Y × M)) T'ᶜ (p + 2 * d)) :
    CompactFiberSlant.Constructions.SupportedProjection.projectSupported d X S K hK T hT p
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
        (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((f, 𝟙 (TopCat.of M)) : (X, TopCat.of M) ⟶ (Y, TopCat.of M)))
        hF (p + 2 * d) c) =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hf p
        (CompactFiberSlant.Constructions.SupportedProjection.projectSupported d Y S' K hK T' hT' p c) := by
  let F : TopCat.of (X × M) ⟶ TopCat.of (Y × M) :=
    AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((f, 𝟙 (TopCat.of M)) : (X, TopCat.of M) ⟶ (Y, TopCat.of M))
  have hP := HodgeConjecture.DegreeTwo.RelativeCrossProduct.Constructions.crossSupportComplement_mapsTo f (𝟙 (TopCat.of M)) hf
    (A := Sᶜ) (A' := S'ᶜ) (B := Kᶜ) (B' := Kᶜ) (fun _ hx => hx)
  have h₁ := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of (X × M))) F
      (CompactFiberSlant.Constructions.SupportedProjection.boundedComplementMapsTo X S K T hT) hF (p + 2 * d)) c
  have h₂ := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) F (𝟙 (TopCat.of (Y × M)))
      hP (CompactFiberSlant.Constructions.SupportedProjection.boundedComplementMapsTo Y S' K T' hT') (p + 2 * d)) c
  have hc := h₁.trans h₂.symm
  refine (congrArg (CompactFiberSlant.Constructions.integrate d X Sᶜ K hK p) hc).trans ?_
  have h := Relative.SlantNaturality.Constructions.slant_natural ℚ f (𝟙 (TopCat.of M)) hf
    (A := Sᶜ) (A' := S'ᶜ) (B := Kᶜ) (B' := Kᶜ) (fun _ hx => hx)
    p (2 * d) (p + 2 * d) rfl (ProperImage.RationalCompactFundamental.Constructions.Construction.rationalCompactFundamentalClass d K hK)
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of (Y × M)))
      (CompactFiberSlant.Constructions.SupportedProjection.boundedComplementMapsTo Y S' K T' hT') (p + 2 * d) c)
  simp only [Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap_id, homologyMap_id, CategoryTheory.id_apply] at h
  exact h

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionNaturality.Constructions
