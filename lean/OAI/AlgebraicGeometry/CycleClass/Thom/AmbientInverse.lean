import OAI.AlgebraicGeometry.CycleClass.Thom.Open.ImageComplement
import OAI.AlgebraicGeometry.CycleClass.Thom.HolomorphicHomeomorph

/-! # Ambient Inverse -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.AmbientInverse.Constructions

noncomputable section

/-! Actual pullback by the inverse of a holomorphic ambient homeomorphism carries the original Thom class to the transported immersion's Thom class. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Degree.Constructions.ThomClass OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.TransportRestriction.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.AmbientNaturality.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.HolomorphicHomeomorph.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {M N N' : Type} [TopologicalSpace N] [TopologicalSpace N'] (f : M → N) (e : N ≃ₜ N')

theorem ambientInverseMapsTo : Set.MapsTo (NormalPair.TransportRestriction.Constructions.ambientTransportMap e.symm)
    (Set.range (e ∘ f))ᶜ (Set.range f)ᶜ := by
  intro y hy h
  obtain ⟨x, hx⟩ := h
  exact hy ⟨x, (congrArg e hx).trans (e.apply_symm_apply y)⟩

theorem ambientImagePair (x : N) : x ∈ (Set.range f)ᶜ ↔ e x ∈ (Set.range (e ∘ f))ᶜ := by
  constructor
  · rintro hx ⟨y, hy⟩
    exact hx ⟨y, e.injective hy⟩
  · rintro hx ⟨y, hy⟩
    exact hx ⟨y, congrArg e hy⟩

theorem ambientInverse_factor : NormalPair.TransportRestriction.Constructions.ambientTransportMap e ≫ NormalPair.TransportRestriction.Constructions.ambientTransportMap e.symm = 𝟙 (TopCat.of N) := by
  ext x
  exact e.symm_apply_apply x

variable {E G H : Type} [TopologicalSpace M]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] [NormedSpace ℝ E]
  [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  [ChartedSpace G N] [IsManifold 𝓘(ℂ, G) ω N] [MetrizableSpace N]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [FiniteDimensional ℂ H]
  [ChartedSpace H N'] [IsManifold 𝓘(ℂ, H) ω N'] [MetrizableSpace N']
  (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, G) ω f)
  (hi : ∀ x, Function.Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, G) f x)) (hc : Topology.IsClosedEmbedding f)
  (he : ContMDiff 𝓘(ℂ, G) 𝓘(ℂ, H) ω e) (hei : ContMDiff 𝓘(ℂ, H) 𝓘(ℂ, G) ω e.symm)

omit [FiniteDimensional ℂ E] [NormedSpace ℝ E] [IsManifold 𝓘(ℂ, E) ω M]
  [FiniteDimensional ℂ G] [IsManifold 𝓘(ℂ, G) ω N] [MetrizableSpace N]
  [FiniteDimensional ℂ H] [IsManifold 𝓘(ℂ, H) ω N'] [MetrizableSpace N'] in
include hf hi he hei in
theorem transported_differential_injective (x : M) :
    Function.Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, H) (e ∘ f) x) := by
  rw [mfderiv_comp x (he.mdifferentiable (by simp) _) (hf.mdifferentiable (by simp) x)]
  exact (HolomorphicHomeomorph.Constructions.homeomorph_mfderiv_bijective e (he.mdifferentiable (by simp))
    (hei.mdifferentiable (by simp)) _).injective.comp (hi x)

theorem ThomClass_ambientInverse (p : ℕ) (hp : Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension E G = p)
    (hpg : Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension E H = p) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (NormalPair.TransportRestriction.Constructions.ambientTransportMap e.symm)
      (ambientInverseMapsTo f e) (2 * p) (Degree.Constructions.ThomClass.complexThomClassInDegree f hf hi hc p hp) =
      Degree.Constructions.ThomClass.complexThomClassInDegree (e ∘ f) (he.comp hf) (transported_differential_injective f e hf hi he hei)
        (e.isClosedEmbedding.comp hc) p hpg := by
  let l := AlgebraicTopology.Duality.Poincare.ImmersionLocalPurity.relativePairHomeomorphCohomologyIso (ModuleCat.of ℚ ℚ)
    (X := TopCat.of N) (Y := TopCat.of N') e (Set.range f)ᶜ (Set.range (e ∘ f))ᶜ (ambientImagePair f e) (2 * p)
  have hl : l.hom = AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (NormalPair.TransportRestriction.Constructions.ambientTransportMap e)
      (NormalPair.TransportRestriction.Constructions.ambientTransportMapsTo f e) (2 * p) := rfl
  apply (ModuleCat.mono_iff_injective l.hom).mp inferInstance
  rw [hl]
  have h₁ := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) (NormalPair.TransportRestriction.Constructions.ambientTransportMap e) (NormalPair.TransportRestriction.Constructions.ambientTransportMap e.symm)
      (NormalPair.TransportRestriction.Constructions.ambientTransportMapsTo f e) (ambientInverseMapsTo f e) (2 * p)) (Degree.Constructions.ThomClass.complexThomClassInDegree f hf hi hc p hp)
  have h₂ := ConcreteCategory.congr_hom (ThomOpenRestriction.Constructions.pairMap_congr (ambientInverse_factor e)
    ((ambientInverseMapsTo f e).comp (NormalPair.TransportRestriction.Constructions.ambientTransportMapsTo f e)) (fun _ hx => hx) (2 * p))
    (Degree.Constructions.ThomClass.complexThomClassInDegree f hf hi hc p hp)
  have h₃ := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_id (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range f)ᶜ (2 * p))
    (Degree.Constructions.ThomClass.complexThomClassInDegree f hf hi hc p hp)
  exact h₁.trans (h₂.trans (h₃.trans (AmbientNaturality.Constructions.complexThomClassInDegree_ambientTransport f hf hi hc e
    (he.mdifferentiable (by simp)) (hei.mdifferentiable (by simp)) (he.comp hf)
    (transported_differential_injective f e hf hi he hei) (e.isClosedEmbedding.comp hc) p hp hpg).symm))

end

end OAI.AlgebraicGeometry.CycleClass.Thom.AmbientInverse.Constructions
