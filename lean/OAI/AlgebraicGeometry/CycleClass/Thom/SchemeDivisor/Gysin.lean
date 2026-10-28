import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ClosedImmersion
import OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Module
import OAI.AlgebraicGeometry.CycleClass.Thom.Normal.GysinRestriction

/-! # Gysin -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Gysin.Constructions

noncomputable section

/-! Genuine supported Gysin pushforward of a canonical, possibly
singular prime divisor, with support in its actual ambient image. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ClosedImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Purity.Constructions
  Module.Constructions Normal.GysinRestriction.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase}
  [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)]
  (i : X ⟶ Y) [IsClosedImmersion i.left]
  (z : {x : X.left // Order.coheight x = 1})

def divisorImageOpen : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) :=
  ⟨(Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ∘ Scheme.RegularSupport.Constructions.supportInclusion X (Purity.Constructions.primeSupport X z)))ᶜ,
    ((ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isClosedEmbedding_map_of_isClosedImmersion i).comp
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isClosedEmbedding_map_of_isClosedImmersion
        (Scheme.RegularSupport.Constructions.supportToAmbient X (Purity.Constructions.primeSupport X z)))).isClosed_range.isOpen_compl⟩

omit [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)] in
theorem divisorImage_mem_iff (y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i y ∉ divisorImageOpen i z ↔
      y ∈ Set.range (Scheme.RegularSupport.Constructions.supportInclusion X (Purity.Constructions.primeSupport X z)) := by
  classical
  change ¬ (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i y ∉ Set.range
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ∘ Scheme.RegularSupport.Constructions.supportInclusion X (Purity.Constructions.primeSupport X z))) ↔ _
  rw [not_not]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isClosedEmbedding_map_of_isClosedImmersion i).injective ht⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t, rfl⟩

omit [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)] in
theorem divisorSourceComplement :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' (divisorImageOpen i z : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) =
      (Set.range (Scheme.RegularSupport.Constructions.supportInclusion X (Purity.Constructions.primeSupport X z)))ᶜ := by
  ext y
  change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i y ∈ divisorImageOpen i z ↔
    y ∉ Set.range (Scheme.RegularSupport.Constructions.supportInclusion X (Purity.Constructions.primeSupport X z))
  simpa only [not_not] using not_congr (divisorImage_mem_iff i z y)

variable (p : ℕ) (hp : Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom + p =
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom)

omit [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem divisorImage_supported :
    (divisorImageOpen i z : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))ᶜ ⊆
      Set.range (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularComplementInclusion := by
  classical
  intro y hy
  change ¬ (y ∉ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ∘ Scheme.RegularSupport.Constructions.supportInclusion X (Purity.Constructions.primeSupport X z))) at hy
  obtain ⟨t, ht⟩ := not_not.mp hy
  exact ⟨Scheme.RegularSupport.Constructions.supportInclusion X (Purity.Constructions.primeSupport X z) t, ht⟩

variable [AlgebraicGeometry.IsNoetherian X.left]
  (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
    (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) (Set.range (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularComplementInclusion)ᶜ) (2 * p))
  (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularThomClass)

def divisorGysinClass : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
    (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) (divisorImageOpen i z : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) (2 * (p + 1)) :=
  (Normal.GysinRestriction.Constructions.globalGysinIso (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp) (divisorImageOpen i z)
    (divisorImage_supported i z p hp) a ha 1).hom
    ((AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (divisorSourceComplement i z) 2).inv
      (Module.Constructions.supportedDivisorClass X z))

end

end OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Gysin.Constructions
