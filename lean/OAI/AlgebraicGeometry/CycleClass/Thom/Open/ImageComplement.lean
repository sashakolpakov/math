import OAI.AlgebraicGeometry.CycleClass.Thom.OpenRestriction
import OAI.AlgebraicGeometry.CycleClass.Thom.AmbientNaturality

/-! # Image Complement -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.Open.ImageComplement.Constructions.ThomAmbientTransport

/-! The actual Thom class on an ambient open remains the actual restricted Thom class after a holomorphic change of ambient coordinates. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.GraphOpenImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.OpenImmersion.Constructions.Raw OAI.AlgebraicGeometry.CycleClass.Thom.Degree.Constructions.ThomClass OAI.AlgebraicGeometry.CycleClass.Thom.OpenRestriction.Constructions.RawThom
open OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.AmbientTransport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.TransportRestriction.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.AmbientNaturality.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {M N N' E G H : Type} [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace N']
  [NormedAddCommGroup E] [NormedSpace ℂ E] [ChartedSpace E M]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [ChartedSpace G N]
  (f : M → N) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, G) ω f) (U : Opens N) (e : U ≃ₜ N')

def transportedOpenMap : TopCat.of N' ⟶ TopCat.of N :=
  TopCat.ofHom ⟨(Subtype.val : U → N) ∘ e.symm, continuous_subtype_val.comp e.symm.continuous⟩

theorem transportedOpenMap_factor :
    NormalPair.TransportRestriction.Constructions.ambientTransportMap e ≫ transportedOpenMap U e = Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of N) (U : Set N) := by
  ext x
  change (e.symm (e x)).val = x.val
  rw [e.symm_apply_apply]

theorem transportedOpenMap_mapsTo : Set.MapsTo (transportedOpenMap U e)
    (Set.range (e ∘ GraphOpenImmersion.Constructions.restrictedBase f hf U))ᶜ (Set.range f)ᶜ := by
  intro y hy h
  obtain ⟨x, hx⟩ := h
  have hxU : f x ∈ U := hx.symm ▸ (e.symm y).property
  apply hy
  refine ⟨⟨x, hxU⟩, ?_⟩
  change e (⟨f x, hxU⟩ : U) = y
  have hs : (⟨f x, hxU⟩ : U) = e.symm y := Subtype.ext hx
  rw [hs, e.apply_symm_apply]

theorem transportedOpen_pair (x : U) :
    x ∈ (Set.range (GraphOpenImmersion.Constructions.restrictedBase f hf U))ᶜ ↔ e x ∈ (Set.range (e ∘ GraphOpenImmersion.Constructions.restrictedBase f hf U))ᶜ := by
  constructor
  · rintro hx ⟨y, hy⟩
    exact hx ⟨y, e.injective hy⟩
  · rintro hx ⟨y, hy⟩
    exact hx ⟨y, congrArg e hy⟩

variable [FiniteDimensional ℂ E] [NormedSpace ℝ E] [IsManifold 𝓘(ℂ, E) ω M]
  [FiniteDimensional ℂ G] [IsManifold 𝓘(ℂ, G) ω N] [MetrizableSpace N]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [FiniteDimensional ℂ H]
  [ChartedSpace H N'] [IsManifold 𝓘(ℂ, H) ω N'] [MetrizableSpace N']
  (hi : ∀ x, Function.Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, G) f x)) (hc : Topology.IsClosedEmbedding f)
  (he : MDifferentiable 𝓘(ℂ, G) 𝓘(ℂ, H) e) (hei : MDifferentiable 𝓘(ℂ, H) 𝓘(ℂ, G) e.symm)
  (hg : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, H) ω (e ∘ GraphOpenImmersion.Constructions.restrictedBase f hf U))
  (hgi : ∀ x, Function.Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, H) (e ∘ GraphOpenImmersion.Constructions.restrictedBase f hf U) x))
  (p : ℕ) (hp : Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension E G = p) (hpg : Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension E H = p)

local instance : MetrizableSpace U := U.isOpenEmbedding'.isEmbedding.metrizableSpace

include he hei in
theorem ThomClass_open_ambientTransport :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (transportedOpenMap U e)
      (transportedOpenMap_mapsTo f hf U e) (2 * p) (Degree.Constructions.ThomClass.complexThomClassInDegree f hf hi hc p hp) =
      Degree.Constructions.ThomClass.complexThomClassInDegree (e ∘ GraphOpenImmersion.Constructions.restrictedBase f hf U) hg hgi
        (e.isClosedEmbedding.comp (OpenImmersion.Constructions.Raw.restrictedBase_closedEmbedding f hf U hc)) p hpg := by
  let l := AlgebraicTopology.Duality.Poincare.ImmersionLocalPurity.relativePairHomeomorphCohomologyIso (ModuleCat.of ℚ ℚ)
    (X := TopCat.of U) (Y := TopCat.of N') e (Set.range (GraphOpenImmersion.Constructions.restrictedBase f hf U))ᶜ
    (Set.range (e ∘ GraphOpenImmersion.Constructions.restrictedBase f hf U))ᶜ (transportedOpen_pair f hf U e) (2 * p)
  have hl : l.hom = AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (NormalPair.TransportRestriction.Constructions.ambientTransportMap e)
      (NormalPair.TransportRestriction.Constructions.ambientTransportMapsTo (GraphOpenImmersion.Constructions.restrictedBase f hf U) e) (2 * p) := rfl
  apply (ModuleCat.mono_iff_injective l.hom).mp inferInstance
  rw [hl]
  have h₁ := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) (NormalPair.TransportRestriction.Constructions.ambientTransportMap e) (transportedOpenMap U e)
      (NormalPair.TransportRestriction.Constructions.ambientTransportMapsTo (GraphOpenImmersion.Constructions.restrictedBase f hf U) e) (transportedOpenMap_mapsTo f hf U e) (2 * p))
    (Degree.Constructions.ThomClass.complexThomClassInDegree f hf hi hc p hp)
  have h₂ := ConcreteCategory.congr_hom (ThomOpenRestriction.Constructions.pairMap_congr (transportedOpenMap_factor U e)
    ((transportedOpenMap_mapsTo f hf U e).comp (NormalPair.TransportRestriction.Constructions.ambientTransportMapsTo (GraphOpenImmersion.Constructions.restrictedBase f hf U) e))
    (OpenImmersion.Constructions.Raw.restriction_mapsTo f hf U) (2 * p)) (Degree.Constructions.ThomClass.complexThomClassInDegree f hf hi hc p hp)
  have h₃ := AmbientNaturality.Constructions.complexThomClassInDegree_ambientTransport (GraphOpenImmersion.Constructions.restrictedBase f hf U) (GraphOpenImmersion.Constructions.restrictedBase_analytic f hf U)
    (OpenImmersion.Constructions.Raw.restrictedBase_differential_injective f hf U hi) (OpenImmersion.Constructions.Raw.restrictedBase_closedEmbedding f hf U hc)
    e he hei hg hgi (e.isClosedEmbedding.comp (OpenImmersion.Constructions.Raw.restrictedBase_closedEmbedding f hf U hc)) p hp hpg
  exact h₁.trans (h₂.trans ((OpenRestriction.Constructions.RawThom.ThomClass_open_restriction f hf hi hc U p hp).trans h₃.symm))

end AlgebraicGeometry.CycleClass.Thom.Open.ImageComplement.Constructions.ThomAmbientTransport

namespace AlgebraicGeometry.CycleClass.Thom.Open.ImageComplement.Constructions

/-! Exact complement pullback for an image transported through an actual
homeomorphism of an ambient open. -/

open _root_.CategoryTheory _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Open.ImageComplement.Constructions.ThomAmbientTransport

variable {N N' L M : Type} [TopologicalSpace N] [TopologicalSpace N']

theorem transportedImage_complement (U : Opens N) (e : U ≃ₜ N')
    (u : L → U) (g : M → N') (A : Set N)
    (hu : Set.range u = (Subtype.val : U → N) ⁻¹' Aᶜ)
    (hg : Set.range (e ∘ u) = Set.range g) :
    (ThomAmbientTransport.transportedOpenMap U e) ⁻¹' A = (Set.range g)ᶜ := by
  ext y
  change (e.symm y).val ∈ A ↔ y ∉ Set.range g
  rw [← hg]
  have hmem : (e.symm y).val ∉ A ↔ y ∈ Set.range (e ∘ u) := by
    rw [← Set.mem_compl_iff, ← Set.mem_preimage, ← hu]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, by simp only [Function.comp_apply, hx, e.apply_symm_apply]⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, by simpa only [Function.comp_apply, e.symm_apply_apply] using congrArg e.symm hx⟩
  simpa only [not_not] using not_congr hmem

end AlgebraicGeometry.CycleClass.Thom.Open.ImageComplement.Constructions

end

end OAI
