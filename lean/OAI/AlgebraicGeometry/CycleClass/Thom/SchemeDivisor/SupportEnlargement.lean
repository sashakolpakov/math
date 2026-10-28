import OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Gysin
import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SupportedPrincipalDivisor
import OAI.AlgebraicGeometry.CycleClass.Thom.Supported.GysinEnlargement
import OAI.AlgebraicGeometry.CycleClass.Thom.Normal.Product
import OAI.AlgebraicGeometry.CycleClass.Thom.ThomOpenRestriction

/-! # Support Enlargement -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.SupportEnlargement.Constructions

noncomputable section

/-! The actual complement-divisor support enlarges to the specified
intersection support, and the canonical source class undergoes the
same literal pair maps as the original supported Gysin construction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ClosedImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Purity.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Module.Constructions
  Gysin.Constructions Scheme.SupportedPrincipalDivisor.Constructions Scheme.FiniteDivisorDetection.Constructions Scheme.SectionEvaluation.Constructions
  Supported.GysinEnlargement.Constructions Normal.Product.Constructions.Class

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  (i : X ⟶ Y) [IsClosedImmersion i.left] (R : X.left.Opens) (z : Scheme.FiniteDivisorDetection.Constructions.ComplementDivisorPoint X R)
  {L : Type} (v : L → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)
  (hR : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' (Set.range v)ᶜ ⊆ (Scheme.SectionEvaluation.Constructions.analyticOpen X R : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)))

omit [IsIntegral X.left] [Smooth X.hom] in
include hR in
theorem complement_le_divisorImageOpen :
    (Set.range v)ᶜ ⊆ (Gysin.Constructions.divisorImageOpen i ⟨z.val, z.property.1⟩ : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) := by
  intro y hy ht
  obtain ⟨t, ht⟩ := ht
  have he : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i (Scheme.RegularSupport.Constructions.supportInclusion X (Scheme.SupportedPrincipalDivisor.Constructions.complementDivisorSupport X R z) t) = y := ht
  have hs : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i (Scheme.RegularSupport.Constructions.supportInclusion X (Scheme.SupportedPrincipalDivisor.Constructions.complementDivisorSupport X R z) t) ∉ Set.range v :=
    (congrArg (fun u => u ∉ Set.range v) he).mpr hy
  exact Scheme.SupportedPrincipalDivisor.Constructions.complementDivisorSupport_complement X R z (hR hs) ⟨t, rfl⟩

omit [IsIntegral X.left] [Smooth X.hom] [IsClosedImmersion i.left] in
include hR in
theorem sourceSupport_mapsTo : Set.MapsTo (𝟙 (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)))
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' (Set.range v)ᶜ) (Set.range (Scheme.RegularSupport.Constructions.supportInclusion X (Scheme.SupportedPrincipalDivisor.Constructions.complementDivisorSupport X R z)))ᶜ :=
  fun _ hy => Scheme.SupportedPrincipalDivisor.Constructions.complementDivisorSupport_complement X R z (hR hy)

variable [IsIntegral Y.left] [Smooth Y.hom]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)]
  [AlgebraicGeometry.IsNoetherian X.left]
  (p : ℕ) (hp : Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom + p = Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom)

theorem enlargedDivisorClass_eq_gysinSource :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))) hR 2
      (Scheme.SupportedPrincipalDivisor.Constructions.complementDivisorSupportedClass X R z) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)))
      (Supported.GysinEnlargement.Constructions.source_mapsTo (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp) (Gysin.Constructions.divisorImageOpen i ⟨z.val, z.property.1⟩) v
        (complement_le_divisorImageOpen i R z v hR)) 2
      ((AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
        (Gysin.Constructions.divisorSourceComplement i ⟨z.val, z.property.1⟩) 2).inv (Module.Constructions.supportedDivisorClass X ⟨z.val, z.property.1⟩)) := by
  have hc := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ)
    (𝟙 (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))) (𝟙 (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))) hR
    (Scheme.SupportedPrincipalDivisor.Constructions.complementDivisorSupport_complement X R z) 2
  have hi := ThomOpenRestriction.Constructions.pairMap_congr (Category.id_comp (𝟙 (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))))
    (fun _ hy => Scheme.SupportedPrincipalDivisor.Constructions.complementDivisorSupport_complement X R z (hR hy)) (sourceSupport_mapsTo i R z v hR) 2
  have hcomp := ConcreteCategory.congr_hom (hc.trans hi) (Module.Constructions.supportedDivisorClass X ⟨z.val, z.property.1⟩)
  have ht := Normal.Product.Constructions.Class.relativeCohomologyMap_targetCast (𝟙 (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)))
    (Gysin.Constructions.divisorSourceComplement i ⟨z.val, z.property.1⟩).symm (sourceSupport_mapsTo i R z v hR)
    (Supported.GysinEnlargement.Constructions.source_mapsTo (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp) (Gysin.Constructions.divisorImageOpen i ⟨z.val, z.property.1⟩) v
      (complement_le_divisorImageOpen i R z v hR)) 2 (Module.Constructions.supportedDivisorClass X ⟨z.val, z.property.1⟩)
  exact hcomp.trans ht.symm

end

end OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.SupportEnlargement.Constructions
