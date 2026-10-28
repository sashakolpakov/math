import OAI.AlgebraicGeometry.CycleClass.Thom.OpenNormalPair
import OAI.AlgebraicGeometry.CycleClass.Thom.Degree
import OAI.AlgebraicGeometry.CycleClass.Thom.FixedNormalPair
import OAI.AlgebraicGeometry.CycleClass.Thom.ThomOpenRestriction

/-! # Open Restriction -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.OpenRestriction.Constructions.RawThom

noncomputable section

/-! The actual Thom class restricts to the Thom class of the actual open immersion restriction for arbitrary complex model spaces, including product models. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.GraphOpenImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.OpenImmersion.Constructions.Raw OAI.AlgebraicGeometry.CycleClass.Thom.OpenNormalPair.Constructions.Raw OAI.AlgebraicGeometry.CycleClass.Thom.Degree.Constructions.ThomClass
open OAI.AlgebraicGeometry.CycleClass.Thom.Open.NormalNeighborhoodInverse.Constructions.PairTransport OAI.AlgebraicGeometry.CycleClass.Thom.FixedNormalPair.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {M N E G : Type} [TopologicalSpace M] [TopologicalSpace N]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] [NormedSpace ℝ E]
  [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  [ChartedSpace G N] [IsManifold 𝓘(ℂ, G) ω N] [MetrizableSpace N]
  (f : M → N) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, G) ω f)
  (hi : ∀ x, Function.Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, G) f x))
  (he : Topology.IsClosedEmbedding f) (U : Opens N) (p : ℕ) (hp : Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension E G = p)

local instance : MetrizableSpace U := U.isOpenEmbedding'.isEmbedding.metrizableSpace

theorem ThomClass_open_normal (x : GraphOpenImmersion.Constructions.graphSourceOpen f hf U)
    (Q : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin p → ℂ) (GraphOpenImmersion.Constructions.restrictedBase f hf U) x)
    (hQ : Q.ambientChart.MDifferentiable 𝓘(ℂ, G) 𝓘(ℂ, E × (Fin p → ℂ))) :
    Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of U)
      (Set.range (GraphOpenImmersion.Constructions.restrictedBase f hf U))ᶜ Q.openNeighborhood (2 * p)
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of N) (U : Set N))
        (OpenImmersion.Constructions.Raw.restriction_mapsTo f hf U) (2 * p) (Degree.Constructions.ThomClass.complexThomClassInDegree f hf hi he p hp)) = Q.rationalClassFin := by
  let P := OpenNormalPair.Constructions.Raw.liftedNormalPair f hf U x Q
  let k := Open.NormalNeighborhoodInverse.Constructions.PairTransport.openTransportNormalNeighborhoodMap Q Subtype.val U.isOpenEmbedding'
  have h₁ := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ)
      (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of U) Q.neighborhood) (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of N) (U : Set N))
      (A := Q.relativeComplement) (B := (Set.range (GraphOpenImmersion.Constructions.restrictedBase f hf U))ᶜ) (C := (Set.range f)ᶜ)
      (fun _ hx => hx) (OpenImmersion.Constructions.Raw.restriction_mapsTo f hf U) (2 * p)) (Degree.Constructions.ThomClass.complexThomClassInDegree f hf hi he p hp)
  have h₂ := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) k (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of N) P.neighborhood)
      (A := Q.relativeComplement) (B := P.relativeComplement) (C := (Set.range f)ᶜ)
      (OpenNormalPair.Constructions.Raw.liftedNeighborhood_mapsTo f hf U x Q) (fun _ hx => hx) (2 * p)) (Degree.Constructions.ThomClass.complexThomClassInDegree f hf hi he p hp)
  have hs := h₁.trans h₂.symm
  change Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of U)
      (Set.range (GraphOpenImmersion.Constructions.restrictedBase f hf U))ᶜ Q.openNeighborhood (2 * p)
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of N) (U : Set N))
        (OpenImmersion.Constructions.Raw.restriction_mapsTo f hf U) (2 * p) (Degree.Constructions.ThomClass.complexThomClassInDegree f hf hi he p hp)) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) k (OpenNormalPair.Constructions.Raw.liftedNeighborhood_mapsTo f hf U x Q) (2 * p)
      (Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of N)
        (Set.range f)ᶜ P.openNeighborhood (2 * p) (Degree.Constructions.ThomClass.complexThomClassInDegree f hf hi he p hp)) at hs
  rw [Degree.Constructions.ThomClass.complexThomClassInDegree_restrict f hf hi he p hp x.val P
    (OpenNormalPair.Constructions.Raw.liftedNormalPair_mdifferentiable f hf U x Q hQ)] at hs
  have hn := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) k P.normalCoordinate
      (OpenNormalPair.Constructions.Raw.liftedNeighborhood_mapsTo f hf U x Q) P.normalCoordinate_mapsTo (2 * p)) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass p)
  rw [Q.rationalClassFin_eq_normalPullback]
  apply hs.trans
  rw [P.rationalClassFin_eq_normalPullback]
  exact hn.trans (ConcreteCategory.congr_hom (ThomOpenRestriction.Constructions.pairMap_congr
    (OpenNormalPair.Constructions.Raw.liftedNeighborhood_normalCoordinate f hf U x Q)
    (P.normalCoordinate_mapsTo.comp (OpenNormalPair.Constructions.Raw.liftedNeighborhood_mapsTo f hf U x Q))
    Q.normalCoordinate_mapsTo (2 * p)) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass p))

theorem ThomClass_open_restriction :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of N) (U : Set N))
      (OpenImmersion.Constructions.Raw.restriction_mapsTo f hf U) (2 * p) (Degree.Constructions.ThomClass.complexThomClassInDegree f hf hi he p hp) =
      Degree.Constructions.ThomClass.complexThomClassInDegree (GraphOpenImmersion.Constructions.restrictedBase f hf U) (GraphOpenImmersion.Constructions.restrictedBase_analytic f hf U)
        (OpenImmersion.Constructions.Raw.restrictedBase_differential_injective f hf U hi) (OpenImmersion.Constructions.Raw.restrictedBase_closedEmbedding f hf U he) p hp := by
  choose P hP _hPa _hPi using (fun x : GraphOpenImmersion.Constructions.graphSourceOpen f hf U =>
    FixedNormalPair.Constructions.exists_analytic_normalPair (GraphOpenImmersion.Constructions.restrictedBase f hf U) (GraphOpenImmersion.Constructions.restrictedBase_analytic f hf U)
      (OpenImmersion.Constructions.Raw.restrictedBase_differential_injective f hf U hi)
      (OpenImmersion.Constructions.Raw.restrictedBase_closedEmbedding f hf U he).isEmbedding p hp x)
  apply Degree.Constructions.ThomClass.complexThomClassInDegree_unique (GraphOpenImmersion.Constructions.restrictedBase f hf U) (GraphOpenImmersion.Constructions.restrictedBase_analytic f hf U)
    (OpenImmersion.Constructions.Raw.restrictedBase_differential_injective f hf U hi) (OpenImmersion.Constructions.Raw.restrictedBase_closedEmbedding f hf U he) p hp P hP
  intro x
  exact ThomClass_open_normal f hf hi he U p hp x (P x) (hP x)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.OpenRestriction.Constructions.RawThom
