import OAI.AlgebraicGeometry.CycleClass.Thom.AmbientInverse
import OAI.AlgebraicGeometry.CycleClass.Thom.ImageInvariant
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.ImageComplement

/-! # Ambient Image -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Open.AmbientImage.Constructions

noncomputable section

/-! Restricting an actual Thom class and changing holomorphic ambient coordinates gives the actual Thom class of any closed immersion with the same geometric image. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.GraphOpenImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.OpenImmersion.Constructions.Raw OAI.AlgebraicGeometry.CycleClass.Thom.Degree.Constructions.ThomClass OAI.AlgebraicGeometry.CycleClass.Thom.AmbientInverse.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Open.ImageComplement.Constructions.ThomAmbientTransport OAI.AlgebraicGeometry.CycleClass.Thom.ImageInvariant.Constructions.RawThom

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {M N N' L E G H F : Type} [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace N'] [TopologicalSpace L]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] [NormedSpace ℝ E]
  [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  [ChartedSpace G N] [IsManifold 𝓘(ℂ, G) ω N] [MetrizableSpace N]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [FiniteDimensional ℂ H]
  [ChartedSpace H N'] [IsManifold 𝓘(ℂ, H) ω N'] [MetrizableSpace N']
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F] [NormedSpace ℝ F]
  [ChartedSpace F L] [IsManifold 𝓘(ℂ, F) ω L]
  (f : M → N) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, G) ω f)
  (hi : ∀ x, Function.Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, G) f x)) (hc : Topology.IsClosedEmbedding f)
  (U : Opens N) (e : U ≃ₜ N')
  (he : ContMDiff 𝓘(ℂ, G) 𝓘(ℂ, H) ω e) (hei : ContMDiff 𝓘(ℂ, H) 𝓘(ℂ, G) ω e.symm)
  (g : L → N') (hg : ContMDiff 𝓘(ℂ, F) 𝓘(ℂ, H) ω g)
  (hgi : ∀ x, Function.Injective (mfderiv 𝓘(ℂ, F) 𝓘(ℂ, H) g x)) (hgc : Topology.IsClosedEmbedding g)
  (q : ℕ) (hp : Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension E G = q) (hgp : Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension F H = q)
  (hdim : Module.finrank ℂ E + q = Module.finrank ℂ H)
  (himage : Set.range (e ∘ GraphOpenImmersion.Constructions.restrictedBase f hf U) = Set.range g)

local instance : MetrizableSpace U := U.isOpenEmbedding'.isEmbedding.metrizableSpace

include himage in
omit [FiniteDimensional ℂ E] [NormedSpace ℝ E] [IsManifold 𝓘(ℂ, E) ω M]
  [FiniteDimensional ℂ G] [IsManifold 𝓘(ℂ, G) ω N] [MetrizableSpace N] [MetrizableSpace N'] [TopologicalSpace L] in
theorem imageTransportMapsTo : Set.MapsTo (ImageComplement.Constructions.ThomAmbientTransport.transportedOpenMap U e) (Set.range g)ᶜ (Set.range f)ᶜ :=
  fun _ hy => ImageComplement.Constructions.ThomAmbientTransport.transportedOpenMap_mapsTo f hf U e (ImageInvariant.Constructions.RawThom.imageMapsTo g (e ∘ GraphOpenImmersion.Constructions.restrictedBase f hf U) himage hy)

include he hei hdim in
theorem ThomClass_open_ambientTransport_of_image :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (ImageComplement.Constructions.ThomAmbientTransport.transportedOpenMap U e)
      (imageTransportMapsTo f hf U e g himage) (2 * q) (Degree.Constructions.ThomClass.complexThomClassInDegree f hf hi hc q hp) =
        Degree.Constructions.ThomClass.complexThomClassInDegree g hg hgi hgc q hgp := by
  let z := e ∘ GraphOpenImmersion.Constructions.restrictedBase f hf U
  have hz := he.comp (GraphOpenImmersion.Constructions.restrictedBase_analytic f hf U)
  have hzi := AmbientInverse.Constructions.transported_differential_injective (N := U) (G := G)
    (GraphOpenImmersion.Constructions.restrictedBase f hf U) e (GraphOpenImmersion.Constructions.restrictedBase_analytic f hf U)
    (OpenImmersion.Constructions.Raw.restrictedBase_differential_injective f hf U hi) he hei
  have hzc := e.isClosedEmbedding.comp (OpenImmersion.Constructions.Raw.restrictedBase_closedEmbedding f hf U hc)
  have hp' : Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension E H = q := by
    change Module.finrank ℂ H - Module.finrank ℂ E = q
    omega
  have ht := ImageComplement.Constructions.ThomAmbientTransport.ThomClass_open_ambientTransport f hf U e hi hc (he.mdifferentiable (by simp))
    (hei.mdifferentiable (by simp)) hz hzi q hp hp'
  have hn := ImageInvariant.Constructions.RawThom.ThomClass_eq_of_image (E := F) (W := E) (G := H) g hg hgi hgc z hz hzi hzc q hgp hp' hdim himage
  have hc' := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of N')) (ImageComplement.Constructions.ThomAmbientTransport.transportedOpenMap U e)
      (ImageInvariant.Constructions.RawThom.imageMapsTo g z himage) (ImageComplement.Constructions.ThomAmbientTransport.transportedOpenMap_mapsTo f hf U e) (2 * q))
    (Degree.Constructions.ThomClass.complexThomClassInDegree f hf hi hc q hp)
  simp only [Category.id_comp] at hc'
  exact hc'.symm.trans
    ((congrArg (fun b => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of N'))
      (ImageInvariant.Constructions.RawThom.imageMapsTo g z himage) (2 * q) b) ht).trans hn)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Open.AmbientImage.Constructions
