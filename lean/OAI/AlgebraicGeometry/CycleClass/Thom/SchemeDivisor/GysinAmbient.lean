import OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.GysinOpen
import OAI.AlgebraicGeometry.CycleClass.Thom.AmbientInverse
import OAI.AlgebraicGeometry.CycleClass.Thom.ImageInvariant

/-! # Gysin Ambient -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.GysinAmbient.Constructions

noncomputable section

/-! The actual divisor Gysin class on a regular ambient open becomes the actual graph-image Thom class after a holomorphic ambient change of coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ClosedImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Purity.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Gysin.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.ImageImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.OpenImmersion.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.GysinOpen.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.AmbientInverse.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Degree.Constructions.ThomClass
open OAI.AlgebraicGeometry.CycleClass.Thom.Open.ImageComplement.Constructions.ThomAmbientTransport OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.TransportRestriction.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)]
  [AlgebraicGeometry.IsNoetherian X.left]
  (i : X ⟶ Y) [IsClosedImmersion i.left] (z : {x : X.left // Order.coheight x = 1})
  (p : ℕ) (hp : Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom + p =
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))
  (hR : ((Subtype.val : U → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) ⁻¹' Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ImageImmersion.Constructions.regularDivisorMap i z))) =
    (Subtype.val : U → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) ⁻¹' (Gysin.Constructions.divisorImageOpen i z : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))ᶜ)
  (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
    (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) (Set.range (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularComplementInclusion)ᶜ) (2 * p))
  (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularThomClass)
  {N H : Type} [TopologicalSpace N] [NormedAddCommGroup H] [NormedSpace ℂ H] [FiniteDimensional ℂ H]
  [ChartedSpace H N] [IsManifold 𝓘(ℂ, H) ω N] [MetrizableSpace N]
  (e : U ≃ₜ N)
  (he : ContMDiff 𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) → ℂ) 𝓘(ℂ, H) ω e)
  (hei : ContMDiff 𝓘(ℂ, H) 𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) → ℂ) ω e.symm)
  (hpg : Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension
    (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension (Scheme.RegularSupport.Constructions.regularOver X (Purity.Constructions.primeSupport X z)).hom) → ℂ) H = p + 1)

local instance : MetrizableSpace U := U.isOpenEmbedding'.isEmbedding.metrizableSpace

theorem divisorGysinClass_ambient_Thom :
    let Z := OpenImmersion.Constructions.divisorOpenImmersion i z p hp U hR
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (Open.ImageComplement.Constructions.ThomAmbientTransport.transportedOpenMap U e)
      (A := (Set.range (e ∘ Z.regularComplementInclusion))ᶜ)
      (B := (Gysin.Constructions.divisorImageOpen i z : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)))
      (fun _ hy => OpenImmersion.Constructions.divisorOpenImmersion_mapsTo i z p hp U hR (AmbientInverse.Constructions.ambientInverseMapsTo Z.regularComplementInclusion e hy))
      (2 * (p + 1)) (Gysin.Constructions.divisorGysinClass i z p hp a ha) =
      Degree.Constructions.ThomClass.complexThomClassInDegree (e ∘ Z.regularComplementInclusion) (he.comp Z.holomorphic)
        (AmbientInverse.Constructions.transported_differential_injective (N := U) (G := Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) → ℂ)
          Z.regularComplementInclusion e Z.holomorphic Z.differential_injective he hei)
        (e.isClosedEmbedding.comp Z.closed) (p + 1) hpg := by
  let Z := OpenImmersion.Constructions.divisorOpenImmersion i z p hp U hR
  have hc := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) (NormalPair.TransportRestriction.Constructions.ambientTransportMap e.symm)
      (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)))
      (AmbientInverse.Constructions.ambientInverseMapsTo Z.regularComplementInclusion e) (OpenImmersion.Constructions.divisorOpenImmersion_mapsTo i z p hp U hR)
      (2 * (p + 1))) (Gysin.Constructions.divisorGysinClass i z p hp a ha)
  have ht := GysinOpen.Constructions.divisorGysinClass_open_Thom i z p hp U hR a ha
  have heq := congrArg (fun b => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (NormalPair.TransportRestriction.Constructions.ambientTransportMap e.symm)
    (AmbientInverse.Constructions.ambientInverseMapsTo Z.regularComplementInclusion e) (2 * (p + 1)) b) ht
  have hn := AmbientInverse.Constructions.ThomClass_ambientInverse (N := U) (N' := N)
    (E := Z.regularAnalyticModel) (G := Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) → ℂ) (H := H)
    Z.regularComplementInclusion e Z.holomorphic Z.differential_injective Z.closed he hei
    (p + 1) Z.regularComplement_complexImmersionCodimension hpg
  exact hc.symm.trans (heq.trans hn)

include he hei hpg in
theorem divisorGysinClass_ambient_Thom_of_image
    {L F : Type} [TopologicalSpace L] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [FiniteDimensional ℂ F] [NormedSpace ℝ F] [ChartedSpace F L] [IsManifold 𝓘(ℂ, F) ω L]
    (g : L → N) (hg : ContMDiff 𝓘(ℂ, F) 𝓘(ℂ, H) ω g)
    (hgi : ∀ x, Function.Injective (mfderiv 𝓘(ℂ, F) 𝓘(ℂ, H) g x)) (hgc : Topology.IsClosedEmbedding g)
    (hgp : Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension F H = p + 1)
    (himage : Set.range (e ∘ (OpenImmersion.Constructions.divisorOpenImmersion i z p hp U hR).regularComplementInclusion) = Set.range g) :
    let Z := OpenImmersion.Constructions.divisorOpenImmersion i z p hp U hR
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (Open.ImageComplement.Constructions.ThomAmbientTransport.transportedOpenMap U e)
      (A := (Set.range g)ᶜ) (B := (Gysin.Constructions.divisorImageOpen i z : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)))
      (fun _ hy => OpenImmersion.Constructions.divisorOpenImmersion_mapsTo i z p hp U hR (AmbientInverse.Constructions.ambientInverseMapsTo Z.regularComplementInclusion e
        (ImageInvariant.Constructions.RawThom.imageMapsTo g (e ∘ Z.regularComplementInclusion) himage hy)))
      (2 * (p + 1)) (Gysin.Constructions.divisorGysinClass i z p hp a ha) = Degree.Constructions.ThomClass.complexThomClassInDegree g hg hgi hgc (p + 1) hgp := by
  let Z := OpenImmersion.Constructions.divisorOpenImmersion i z p hp U hR
  have hdim : Module.finrank ℂ Z.regularAnalyticModel + (p + 1) = Module.finrank ℂ H := by
    change Module.finrank ℂ H - Module.finrank ℂ Z.regularAnalyticModel = p + 1 at hpg
    omega
  have hc := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of N)) (Open.ImageComplement.Constructions.ThomAmbientTransport.transportedOpenMap U e)
      (ImageInvariant.Constructions.RawThom.imageMapsTo g (e ∘ Z.regularComplementInclusion) himage)
      (fun _ hy => OpenImmersion.Constructions.divisorOpenImmersion_mapsTo i z p hp U hR (AmbientInverse.Constructions.ambientInverseMapsTo Z.regularComplementInclusion e hy))
      (2 * (p + 1))) (Gysin.Constructions.divisorGysinClass i z p hp a ha)
  simp only [Category.id_comp] at hc
  have ht := congrArg (fun b => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of N))
    (ImageInvariant.Constructions.RawThom.imageMapsTo g (e ∘ Z.regularComplementInclusion) himage) (2 * (p + 1)) b)
    (divisorGysinClass_ambient_Thom i z p hp U hR a ha e he hei hpg)
  have hi := ImageInvariant.Constructions.RawThom.ThomClass_eq_of_image
    (E := F) (W := Z.regularAnalyticModel) (G := H) g hg hgi hgc (e ∘ Z.regularComplementInclusion)
    (he.comp Z.holomorphic)
    (AmbientInverse.Constructions.transported_differential_injective (N := U) (G := Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) → ℂ)
      Z.regularComplementInclusion e Z.holomorphic Z.differential_injective he hei)
    (e.isClosedEmbedding.comp Z.closed) (p + 1) hgp hpg hdim himage
  exact hc.symm.trans (ht.trans hi)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.GysinAmbient.Constructions
