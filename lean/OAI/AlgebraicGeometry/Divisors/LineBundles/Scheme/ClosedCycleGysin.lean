import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ClosedImmersion
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SupportedCycleClass
import OAI.AlgebraicGeometry.CycleClass.Thom.Normal.GysinRestriction

/-! # Closed Cycle Gysin -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.ClosedCycleGysin.BundleCycles

noncomputable section

/-! Genuine supported Gysin pushforward of a canonical cycle in arbitrary codimension, retaining its full possibly singular ambient support. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ClosedImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions
  CycleClass.Thom.Normal.GysinRestriction.Constructions

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase}
  [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)]
  (i : X ⟶ Y) [IsClosedImmersion i.left]
  (Z : IrreducibleCloseds X.left)

def schemeClosedCycleImageOpen : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) :=
  ⟨(Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ∘ CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X Z))ᶜ,
    ((ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isClosedEmbedding_map_of_isClosedImmersion i).comp
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isClosedEmbedding_map_of_isClosedImmersion
        (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportToAmbient X Z))).isClosed_range.isOpen_compl⟩

omit [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)] in
theorem schemeClosedCycleImage_mem_iff (y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i y ∉ schemeClosedCycleImageOpen i Z ↔
      y ∈ Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X Z) := by
  classical
  change ¬ (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i y ∉ Set.range
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ∘ CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X Z)) ↔ _
  rw [not_not]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isClosedEmbedding_map_of_isClosedImmersion i).injective ht⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t, rfl⟩

omit [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)] in
theorem schemeClosedCycleSourceComplement :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' (schemeClosedCycleImageOpen i Z : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) =
      (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X Z))ᶜ := by
  ext y
  change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i y ∈ schemeClosedCycleImageOpen i Z ↔
    y ∉ Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X Z)
  simpa only [not_not] using not_congr (schemeClosedCycleImage_mem_iff i Z y)

variable (p : ℕ) (hp : Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom + p =
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom)

omit [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem schemeClosedCycleImage_supported :
    (schemeClosedCycleImageOpen i Z : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))ᶜ ⊆
      Set.range (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularComplementInclusion := by
  classical
  intro y hy
  change ¬ (y ∉ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ∘ CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X Z)) at hy
  obtain ⟨t, ht⟩ := not_not.mp hy
  exact ⟨CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X Z t, ht⟩

variable [AlgebraicGeometry.IsNoetherian X.left]
  (q : ℕ) (hq : Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.hom + q = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)
  (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
    (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) (Set.range (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularComplementInclusion)ᶜ) (2 * p))
  (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularThomClass)

def schemeClosedCycleGysinClass : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
    (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) (schemeClosedCycleImageOpen i Z : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) (2 * (p + q)) :=
  (CycleClass.Thom.Normal.GysinRestriction.Constructions.globalGysinIso (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp) (schemeClosedCycleImageOpen i Z)
    (schemeClosedCycleImage_supported i Z p hp) a ha q).hom
    ((AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (schemeClosedCycleSourceComplement i Z) (2 * q)).inv
      (SupportedCycleClass.BundleCycles.schemeSupportedCycleClass X Z q hq))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.ClosedCycleGysin.BundleCycles
