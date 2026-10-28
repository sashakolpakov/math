import OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.AmbientTransport
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCohomologySections

/-! # Transport Restriction -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.TransportRestriction.Constructions

noncomputable section

/-! Pullback along an ambient homeomorphism commutes with restriction to
the transported actual normal neighborhood. -/

open _root_.CategoryTheory _root_.TopologicalSpace OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCohomologySections.Cycles

open OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.AmbientTransport.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {M N N' : Type} [TopologicalSpace N] [TopologicalSpace N']
  (f : M → N) (e : N ≃ₜ N')

def ambientTransportMap : TopCat.of N ⟶ TopCat.of N' := TopCat.ofHom ⟨e, e.continuous⟩

theorem ambientTransportMapsTo : Set.MapsTo (ambientTransportMap e)
    (Set.range f)ᶜ (Set.range (e ∘ f))ᶜ := by
  intro z hz h
  obtain ⟨a, ha⟩ := h
  exact hz ⟨a, e.injective ha⟩

variable {E F : Type} [NormedAddCommGroup E] [NormedAddCommGroup F]
  {x : M} (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E F f x)

theorem transportNormalNeighborhoodMap_inclusion :
    AmbientTransport.Constructions.transportNormalNeighborhoodMap P e ≫
      Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of N') (AmbientTransport.Constructions.transportNormalPair P e).neighborhood =
    Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of N) P.neighborhood ≫ (ambientTransportMap e) := by
  ext z
  rfl

theorem ambientTransport_normalRestriction (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (ambientTransportMap e)
      (ambientTransportMapsTo f e) n ≫
      Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of N)
        (Set.range f)ᶜ P.openNeighborhood n =
    Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of N')
      (Set.range (e ∘ f))ᶜ (AmbientTransport.Constructions.transportNormalPair P e).openNeighborhood n ≫
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (AmbientTransport.Constructions.transportNormalNeighborhoodMap P e)
        (AmbientTransport.Constructions.transportNormalNeighborhoodMap_mapsTo P e) n := by
  have h₁ := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ)
    (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of N) P.neighborhood) (ambientTransportMap e)
    (show Set.MapsTo (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of N) P.neighborhood) P.relativeComplement
      (Set.range f)ᶜ from fun _ hz => hz) (ambientTransportMapsTo f e) n
  have h₂ := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ)
    (AmbientTransport.Constructions.transportNormalNeighborhoodMap P e)
    (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of N') (AmbientTransport.Constructions.transportNormalPair P e).neighborhood)
    (AmbientTransport.Constructions.transportNormalNeighborhoodMap_mapsTo P e)
    (show Set.MapsTo (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of N') (AmbientTransport.Constructions.transportNormalPair P e).neighborhood)
      (AmbientTransport.Constructions.transportNormalPair P e).relativeComplement (Set.range (e ∘ f))ᶜ from fun _ hz => hz) n
  simp only [transportNormalNeighborhoodMap_inclusion f e P] at h₂
  exact h₁.trans h₂.symm

variable [NormedSpace ℝ E]

theorem ambientTransport_normalizedRestriction {p : ℕ}
    (Q : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin p → ℂ) f x)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N') (Set.range (e ∘ f))ᶜ (2 * p))
    (ha : Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of N')
      (Set.range (e ∘ f))ᶜ (AmbientTransport.Constructions.transportNormalPair Q e).openNeighborhood (2 * p) a =
        (AmbientTransport.Constructions.transportNormalPair Q e).rationalClassFin) :
    Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of N)
      (Set.range f)ᶜ Q.openNeighborhood (2 * p)
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (ambientTransportMap e)
        (ambientTransportMapsTo f e) (2 * p) a) = Q.rationalClassFin := by
  have h := ConcreteCategory.congr_hom (ambientTransport_normalRestriction f e Q (2 * p)) a
  simp only [ConcreteCategory.comp_apply, ha] at h
  exact h.trans (AmbientTransport.Constructions.transportNormalClass e Q)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.TransportRestriction.Constructions
