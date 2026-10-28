import OAI.AlgebraicGeometry.CycleClass.Thom.Open.NormalNeighborhoodInverse
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCohomologySections

/-! # Normal Pair Restriction -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Open.NormalPairRestriction.Constructions

noncomputable section

/-! Actual pair pullback along an open ambient embedding commutes with
normal-neighborhood restriction and preserves its normalized class. -/

open _root_.CategoryTheory _root_.TopologicalSpace OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCohomologySections.Cycles

open OAI.AlgebraicGeometry.CycleClass.Thom.Open.NormalNeighborhoodInverse.Constructions.PairTransport

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {M N N' : Type} [TopologicalSpace N] [TopologicalSpace N']
  (f : M → N) (e : N → N') (he : Topology.IsOpenEmbedding e)

def openAmbientTransportMap : TopCat.of N ⟶ TopCat.of N' := TopCat.ofHom ⟨e, he.continuous⟩

theorem openAmbientTransportMapsTo : Set.MapsTo (openAmbientTransportMap e he)
    (Set.range f)ᶜ (Set.range (e ∘ f))ᶜ := by
  intro z hz h
  obtain ⟨a, ha⟩ := h
  exact hz ⟨a, he.injective ha⟩

variable {E F : Type} [NormedAddCommGroup E] [NormedAddCommGroup F]
  {x : M} (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E F f x)

theorem openTransportNormalNeighborhoodMap_inclusion :
    NormalNeighborhoodInverse.Constructions.PairTransport.openTransportNormalNeighborhoodMap P e he ≫
      Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of N') (NormalNeighborhoodInverse.Constructions.PairTransport.openTransportNormalPair P e he).neighborhood =
    Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of N) P.neighborhood ≫ openAmbientTransportMap e he := by
  ext z
  rfl

theorem openAmbientTransport_normalRestriction (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (openAmbientTransportMap e he)
      (openAmbientTransportMapsTo f e he) n ≫
      Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of N)
        (Set.range f)ᶜ P.openNeighborhood n =
    Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of N')
      (Set.range (e ∘ f))ᶜ (NormalNeighborhoodInverse.Constructions.PairTransport.openTransportNormalPair P e he).openNeighborhood n ≫
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (NormalNeighborhoodInverse.Constructions.PairTransport.openTransportNormalNeighborhoodMap P e he)
        (NormalNeighborhoodInverse.Constructions.PairTransport.openTransportNormalNeighborhoodMap_mapsTo P e he) n := by
  have h₁ := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ)
    (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of N) P.neighborhood) (openAmbientTransportMap e he)
    (show Set.MapsTo (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of N) P.neighborhood) P.relativeComplement
      (Set.range f)ᶜ from fun _ hz => hz) (openAmbientTransportMapsTo f e he) n
  have h₂ := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ)
    (NormalNeighborhoodInverse.Constructions.PairTransport.openTransportNormalNeighborhoodMap P e he)
    (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of N') (NormalNeighborhoodInverse.Constructions.PairTransport.openTransportNormalPair P e he).neighborhood)
    (NormalNeighborhoodInverse.Constructions.PairTransport.openTransportNormalNeighborhoodMap_mapsTo P e he)
    (show Set.MapsTo (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of N') (NormalNeighborhoodInverse.Constructions.PairTransport.openTransportNormalPair P e he).neighborhood)
      (NormalNeighborhoodInverse.Constructions.PairTransport.openTransportNormalPair P e he).relativeComplement (Set.range (e ∘ f))ᶜ from fun _ hz => hz) n
  simp only [openTransportNormalNeighborhoodMap_inclusion f e he P] at h₂
  exact h₁.trans h₂.symm

variable [NormedSpace ℝ E]

theorem openAmbientTransport_normalizedRestriction {p : ℕ}
    (Q : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin p → ℂ) f x)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N') (Set.range (e ∘ f))ᶜ (2 * p))
    (ha : Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of N')
      (Set.range (e ∘ f))ᶜ (NormalNeighborhoodInverse.Constructions.PairTransport.openTransportNormalPair Q e he).openNeighborhood (2 * p) a =
        (NormalNeighborhoodInverse.Constructions.PairTransport.openTransportNormalPair Q e he).rationalClassFin) :
    Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of N)
      (Set.range f)ᶜ Q.openNeighborhood (2 * p)
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (openAmbientTransportMap e he)
        (openAmbientTransportMapsTo f e he) (2 * p) a) = Q.rationalClassFin := by
  have h := ConcreteCategory.congr_hom (openAmbientTransport_normalRestriction f e he Q (2 * p)) a
  simp only [ConcreteCategory.comp_apply, ha] at h
  exact h.trans (NormalNeighborhoodInverse.Constructions.PairTransport.openTransportNormalClass e he Q)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Open.NormalPairRestriction.Constructions
