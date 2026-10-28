import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.ClosedCycleGysin
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SupportAmbientNormalPair
import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.OpenImmersion

/-! # Closed Cycle Image Immersion -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.ClosedCycleImageImmersion.BundleCycles

noncomputable section

/-! On the constructed regular-source neighborhoods, the actual
ambient image of a possibly singular source divisor is a closed
complex immersion of the expected codimension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ClosedImmersion.Constructions
  CycleClass.Thom.Scheme.RegularSupport.Constructions CycleClass.Thom.Scheme.OpenImmersion.Constructions

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase}
  [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)]
  (i : X ⟶ Y) [IsClosedImmersion i.left]
  (Z : IrreducibleCloseds X.left)

def schemeRegularClosedCycleMap : CycleClass.Thom.Scheme.RegularSupport.Constructions.regularOver X Z ⟶ Y := CycleClass.Thom.Scheme.RegularSupport.Constructions.regularToAmbient X Z ≫ i

instance schemeRegularClosedCycleMap_immersion : IsImmersion (schemeRegularClosedCycleMap i Z).left := by
  change IsImmersion ((CycleClass.Thom.Scheme.RegularSupport.Constructions.regularToAmbient X Z).left ≫ i.left)
  infer_instance

omit [IsIntegral X.left] [IsIntegral Y.left] [Smooth Y.hom]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)] [IsClosedImmersion i.left] in
theorem schemeRegularClosedCycleMap_apply (t : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularOver X Z)) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (schemeRegularClosedCycleMap i Z) t = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularInclusion X Z t) :=
  ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularToAmbient X Z) i t

variable (p : ℕ) (hp : Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom + p =
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom)
  (q : ℕ) (hq : Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.hom + q = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)
  (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularOver X Z))
  (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularAnalyticModel (Fin p → ℂ)
    (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularComplementInclusion (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularInclusion X Z x))
  (hP : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' P.neighborhood ⊆ (SupportAmbientNormalPair.BundleCycles.schemeSupportAmbientPair X Z q hq x).neighborhood)

include hP in
theorem schemeRegularClosedCycleRange :
    (Subtype.val ⁻¹' Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (schemeRegularClosedCycleMap i Z)) : Set P.openNeighborhood) =
      Subtype.val ⁻¹' (ClosedCycleGysin.BundleCycles.schemeClosedCycleImageOpen i Z : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))ᶜ := by
  classical
  ext y
  constructor
  · rintro ⟨t, ht⟩
    change y.val ∉ ClosedCycleGysin.BundleCycles.schemeClosedCycleImageOpen i Z
    rw [← ht, schemeRegularClosedCycleMap_apply]
    exact (ClosedCycleGysin.BundleCycles.schemeClosedCycleImage_mem_iff i Z _).mpr
      (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularInclusion_subset X Z ⟨t, rfl⟩)
  · intro hy
    have hy' : y.val ∈ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ∘ CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X Z) :=
      not_not.mp hy
    obtain ⟨t, ht⟩ := hy'
    have ht' : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X Z t) = y.val := ht
    have htP : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X Z t) ∈ P.neighborhood :=
      ht'.symm ▸ y.property
    have htG := SupportAmbientNormalPair.BundleCycles.schemeSupportAmbientPair_avoids_boundary X Z q hq x (hP htP)
    have hreg : CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X Z t ∈ Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularInclusion X Z) := by
      by_contra hn
      apply htG
      rw [CycleClass.Thom.Scheme.RegularSupport.Constructions.analyticBoundary_eq]
      exact ⟨⟨t, rfl⟩, hn⟩
    obtain ⟨u, hu⟩ := hreg
    refine ⟨u, ?_⟩
    rw [schemeRegularClosedCycleMap_apply, hu]
    exact ht

omit [Smooth Y.hom] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)] in
include hp hq in
theorem schemeClosedCycleImageCodimension :
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularOver X Z).hom + (p + q) =
      Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom := by
  have hr := CycleClass.Thom.Scheme.RegularSupport.Constructions.regularDimension_eq X Z
  have hX := Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension X.hom
  omega

def schemeLocalClosedCycleImmersion : CycleClass.Thom.Closed.ComplexImmersion.Constructions.ClosedComplexImmersion (CycleClass.Thom.Open.ClosedImmersionComposition.Constructions.ComplexManifold.openManifold (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeManifold Y) P.openNeighborhood) (p + q) :=
  CycleClass.Thom.Scheme.OpenImmersion.Constructions.restrictedImmersion (schemeRegularClosedCycleMap i Z) P.openNeighborhood (p + q) (schemeClosedCycleImageCodimension Z p hp q hq) (by
    rw [schemeRegularClosedCycleRange i Z p hp q hq x P hP]
    exact (ClosedCycleGysin.BundleCycles.schemeClosedCycleImageOpen i Z).isOpen.isClosed_compl.preimage continuous_subtype_val)

theorem schemeLocalClosedCycleImmersion_range : Set.range (schemeLocalClosedCycleImmersion i Z p hp q hq x P hP).regularComplementInclusion =
    Subtype.val ⁻¹' (ClosedCycleGysin.BundleCycles.schemeClosedCycleImageOpen i Z : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))ᶜ :=
  (CycleClass.Thom.Scheme.OpenImmersion.Constructions.restrictedMap_range (schemeRegularClosedCycleMap i Z) P.openNeighborhood).trans (schemeRegularClosedCycleRange i Z p hp q hq x P hP)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.ClosedCycleImageImmersion.BundleCycles
