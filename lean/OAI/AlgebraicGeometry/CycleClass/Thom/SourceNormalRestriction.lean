import OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.SourceTransport
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCohomologySections

/-! # Source Normal Restriction -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.SourceNormalRestriction.Constructions

noncomputable section

/-! The actual supported pullback for a surjective source reparametrization
preserves the normal-class restriction. -/

open _root_.CategoryTheory OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCohomologySections.Cycles

open OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.SourceTransport.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {M M' N : Type} [TopologicalSpace N] (f : M → N)
  (a : M' → M) (ha : Function.Surjective a)

include ha in
theorem sourceAmbientMapsTo : Set.MapsTo (𝟙 (TopCat.of N)) (Set.range (f ∘ a))ᶜ (Set.range f)ᶜ := by
  intro z hz
  change z ∉ Set.range f
  rwa [NormalPair.SourceTransport.Constructions.sourceTransport_range a ha] at hz

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (x : M') {p : ℕ} (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin p → ℂ) f (a x))

theorem sourceTransport_normalizedRestriction
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range f)ᶜ (2 * p))
    (hb : Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of N)
      (Set.range f)ᶜ P.openNeighborhood (2 * p) b = P.rationalClassFin) :
    Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of N)
      (Set.range (f ∘ a))ᶜ (NormalPair.SourceTransport.Constructions.sourceTransportNormalPair a ha x P).openNeighborhood (2 * p)
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of N))
        (sourceAmbientMapsTo f a ha) (2 * p) b) =
      (NormalPair.SourceTransport.Constructions.sourceTransportNormalPair a ha x P).rationalClassFin := by
  have h₁ := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ)
    (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of N) (NormalPair.SourceTransport.Constructions.sourceTransportNormalPair a ha x P).neighborhood)
    (𝟙 (TopCat.of N))
    (show Set.MapsTo (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of N) (NormalPair.SourceTransport.Constructions.sourceTransportNormalPair a ha x P).neighborhood)
      (NormalPair.SourceTransport.Constructions.sourceTransportNormalPair a ha x P).relativeComplement (Set.range (f ∘ a))ᶜ from fun _ hz => hz)
    (sourceAmbientMapsTo f a ha) (2 * p)
  have h₂ := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ)
    (NormalPair.SourceTransport.Constructions.sourceTransportNeighborhoodMap a ha x P) (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of N) P.neighborhood)
    (NormalPair.SourceTransport.Constructions.sourceTransportNeighborhoodMap_mapsTo a ha x P)
    (show Set.MapsTo (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of N) P.neighborhood) P.relativeComplement
      (Set.range f)ᶜ from fun _ hz => hz) (2 * p)
  simp only [Category.comp_id] at h₁
  simp only [NormalPair.SourceTransport.Constructions.sourceTransportNeighborhoodMap, Category.id_comp] at h₂
  have h := ConcreteCategory.congr_hom (h₁.trans h₂.symm) b
  change Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of N)
    (Set.range (f ∘ a))ᶜ (NormalPair.SourceTransport.Constructions.sourceTransportNormalPair a ha x P).openNeighborhood (2 * p)
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of N))
      (sourceAmbientMapsTo f a ha) (2 * p) b) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (NormalPair.SourceTransport.Constructions.sourceTransportNeighborhoodMap a ha x P)
      (NormalPair.SourceTransport.Constructions.sourceTransportNeighborhoodMap_mapsTo a ha x P) (2 * p)
      (Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of N)
        (Set.range f)ᶜ P.openNeighborhood (2 * p) b) at h
  rw [hb] at h
  exact h.trans (NormalPair.SourceTransport.Constructions.sourceTransportNormalClass a ha x P)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.SourceNormalRestriction.Constructions
