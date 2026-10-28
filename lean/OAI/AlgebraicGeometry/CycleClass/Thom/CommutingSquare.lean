import OAI.AlgebraicGeometry.CycleClass.Thom.AmbientNaturality
import OAI.AlgebraicGeometry.CycleClass.Thom.SourceNaturality
import OAI.AlgebraicGeometry.CycleClass.Thom.HolomorphicHomeomorphDerivative

/-! # Commuting Square -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.CommutingSquare.Constructions

noncomputable section

/-! Naturality of the genuine Thom class for an actual commuting square
with holomorphic ambient homeomorphism and surjective source parametrization. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Degree.Constructions.ThomClass OAI.AlgebraicGeometry.CycleClass.Thom.AmbientNaturality.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SourceNaturality.Constructions
  NormalPair.TransportRestriction.Constructions SourceNormalRestriction.Constructions HolomorphicHomeomorphDerivative.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {M M' N N' : Type} [TopologicalSpace N] [TopologicalSpace N']

include N N' in
theorem squareMapsTo (f : M → N) (g : M' → N') (e : N ≃ₜ N')
    (a : M → M') (ha : Function.Surjective a) (hcomm : e ∘ f = g ∘ a) :
    Set.MapsTo (NormalPair.TransportRestriction.Constructions.ambientTransportMap e) (Set.range f)ᶜ (Set.range g)ᶜ := by
  intro z hz hg
  obtain ⟨b, hb⟩ := hg
  obtain ⟨x, rfl⟩ := ha b
  exact hz ⟨x, e.injective ((congrFun hcomm x).trans hb)⟩

variable {E F G H : Type}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [FiniteDimensional ℂ H]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M]
  [TopologicalSpace M'] [ChartedSpace G M'] [IsManifold 𝓘(ℂ, G) ω M']
  [ChartedSpace F N] [IsManifold 𝓘(ℂ, F) ω N] [MetrizableSpace N]
  [ChartedSpace H N'] [IsManifold 𝓘(ℂ, H) ω N'] [MetrizableSpace N']

theorem complexThomClassInDegree_commutingSquare
    (f : M → N) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ω f)
    (hfi : ∀ x, Function.Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) f x))
    (hfc : Topology.IsClosedEmbedding f)
    (g : M' → N') (hg : ContMDiff 𝓘(ℂ, G) 𝓘(ℂ, H) ω g)
    (hgi : ∀ x, Function.Injective (mfderiv 𝓘(ℂ, G) 𝓘(ℂ, H) g x))
    (hgc : Topology.IsClosedEmbedding g)
    (e : N ≃ₜ N') (he : ContMDiff 𝓘(ℂ, F) 𝓘(ℂ, H) ω e)
    (hei : MDifferentiable 𝓘(ℂ, H) 𝓘(ℂ, F) e.symm)
    (a : M → M') (ha : Function.Surjective a) (hcomm : e ∘ f = g ∘ a)
    (l : G ≃L[ℂ] E) (hl : ∀ v, ‖l v‖ = ‖v‖)
    (p : ℕ) (hpf : Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension E F = p)
    (hpg : Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension G H = p)
    (hpe : Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension E H = p) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (NormalPair.TransportRestriction.Constructions.ambientTransportMap e)
      (squareMapsTo f g e a ha hcomm) (2 * p)
      (Degree.Constructions.ThomClass.complexThomClassInDegree g hg hgi hgc p hpg) =
      Degree.Constructions.ThomClass.complexThomClassInDegree f hf hfi hfc p hpf := by
  have hef := he.comp hf
  have hefi : ∀ x, Function.Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, H) (e ∘ f) x) :=
    HolomorphicHomeomorphDerivative.Constructions.comp_mfderiv_injective f e (hf.mdifferentiable (by simp)) (he.mdifferentiable (by simp)) hfi
      (HolomorphicHomeomorphDerivative.Constructions.homeomorph_mfderiv_injective e (he.mdifferentiable (by simp)) hei)
  have hefc : Topology.IsClosedEmbedding (e ∘ f) := e.isClosedEmbedding.comp hfc
  have hga : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, H) ω (g ∘ a) := hcomm ▸ hef
  have hgai : ∀ x, Function.Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, H) (g ∘ a) x) := hcomm ▸ hefi
  have hgac : Topology.IsClosedEmbedding (g ∘ a) := hcomm ▸ hefc
  have hs := SourceNaturality.Constructions.complexThomClassInDegree_sourceTransport g hg hgi hgc a ha l hl hga hgai hgac p hpg hpe
  have ht := AmbientNaturality.Constructions.complexThomClassInDegree_ambientTransport f hf hfi hfc e
    (he.mdifferentiable (by simp)) hei hef hefi hefc p hpf hpe
  have hpair : Set.MapsTo (NormalPair.TransportRestriction.Constructions.ambientTransportMap e) (Set.range f)ᶜ (Set.range (g ∘ a))ᶜ := by
    rw [← hcomm]
    exact NormalPair.TransportRestriction.Constructions.ambientTransportMapsTo f e
  have hrestrict : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (NormalPair.TransportRestriction.Constructions.ambientTransportMap e)
      hpair (2 * p) (Degree.Constructions.ThomClass.complexThomClassInDegree (g ∘ a) hga hgai hgac p hpe) =
      Degree.Constructions.ThomClass.complexThomClassInDegree f hf hfi hfc p hpf := by
    clear hs
    generalize hgf : g ∘ a = k at *
    have hk : k = e ∘ f := hcomm.symm
    subst hk
    exact ht
  rw [← hs] at hrestrict
  have hm := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ)
    (NormalPair.TransportRestriction.Constructions.ambientTransportMap e) (𝟙 (TopCat.of N')) hpair (SourceNormalRestriction.Constructions.sourceAmbientMapsTo g a ha) (2 * p)
  simp only [Category.comp_id] at hm
  have hv := ConcreteCategory.congr_hom hm (Degree.Constructions.ThomClass.complexThomClassInDegree g hg hgi hgc p hpg)
  change AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (NormalPair.TransportRestriction.Constructions.ambientTransportMap e) hpair (2 * p)
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of N'))
      (SourceNormalRestriction.Constructions.sourceAmbientMapsTo g a ha) (2 * p) (Degree.Constructions.ThomClass.complexThomClassInDegree g hg hgi hgc p hpg)) = _ at hv
  exact hv.symm.trans hrestrict

end

end OAI.AlgebraicGeometry.CycleClass.Thom.CommutingSquare.Constructions
