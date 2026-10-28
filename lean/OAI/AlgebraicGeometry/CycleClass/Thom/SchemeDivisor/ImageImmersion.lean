import OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.OuterPair
import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.OpenImmersion

/-! # Image Immersion -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.ImageImmersion.Constructions

noncomputable section

/-! On the constructed regular-source neighborhoods, the actual
ambient image of a possibly singular source divisor is a closed
complex immersion of the expected codimension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ClosedImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Purity.Constructions
  Gysin.Constructions Scheme.PrimeAmbientNormalPair.Constructions Scheme.OpenImmersion.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase}
  [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)]
  (i : X ⟶ Y) [IsClosedImmersion i.left]
  (z : {x : X.left // Order.coheight x = 1})

def regularDivisorMap : Scheme.RegularSupport.Constructions.regularOver X (Purity.Constructions.primeSupport X z) ⟶ Y := Scheme.RegularSupport.Constructions.regularToAmbient X (Purity.Constructions.primeSupport X z) ≫ i

instance regularDivisorMap_immersion : IsImmersion (regularDivisorMap i z).left := by
  change IsImmersion ((Scheme.RegularSupport.Constructions.regularToAmbient X (Purity.Constructions.primeSupport X z)).left ≫ i.left)
  infer_instance

omit [IsIntegral X.left] [IsIntegral Y.left] [Smooth Y.hom]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)] [IsClosedImmersion i.left] in
theorem regularDivisorMap_apply (t : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Scheme.RegularSupport.Constructions.regularOver X (Purity.Constructions.primeSupport X z))) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (regularDivisorMap i z) t = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i (Scheme.RegularSupport.Constructions.regularInclusion X (Purity.Constructions.primeSupport X z) t) :=
  ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp (Scheme.RegularSupport.Constructions.regularToAmbient X (Purity.Constructions.primeSupport X z)) i t

variable (p : ℕ) (hp : Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom + p =
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom)
  (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Scheme.RegularSupport.Constructions.regularOver X (Purity.Constructions.primeSupport X z)))
  (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularAnalyticModel (Fin p → ℂ)
    (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularComplementInclusion (Scheme.RegularSupport.Constructions.regularInclusion X (Purity.Constructions.primeSupport X z) x))
  (hP : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' P.neighborhood ⊆ (Scheme.PrimeAmbientNormalPair.Constructions.primeAmbientPair X z x).neighborhood)

include hP in
theorem regularDivisorRange :
    (Subtype.val ⁻¹' Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (regularDivisorMap i z)) : Set P.openNeighborhood) =
      Subtype.val ⁻¹' (Gysin.Constructions.divisorImageOpen i z : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))ᶜ := by
  classical
  ext y
  constructor
  · rintro ⟨t, ht⟩
    change y.val ∉ Gysin.Constructions.divisorImageOpen i z
    rw [← ht, regularDivisorMap_apply]
    exact (Gysin.Constructions.divisorImage_mem_iff i z _).mpr
      (Scheme.RegularSupport.Constructions.regularInclusion_subset X (Purity.Constructions.primeSupport X z) ⟨t, rfl⟩)
  · intro hy
    have hy' : y.val ∈ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ∘ Scheme.RegularSupport.Constructions.supportInclusion X (Purity.Constructions.primeSupport X z)) :=
      not_not.mp hy
    obtain ⟨t, ht⟩ := hy'
    have ht' : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i (Scheme.RegularSupport.Constructions.supportInclusion X (Purity.Constructions.primeSupport X z) t) = y.val := ht
    have htP : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i (Scheme.RegularSupport.Constructions.supportInclusion X (Purity.Constructions.primeSupport X z) t) ∈ P.neighborhood :=
      ht'.symm ▸ y.property
    have htG := Scheme.PrimeAmbientNormalPair.Constructions.primeAmbientPair_avoids_boundary X z x (hP htP)
    have hreg : Scheme.RegularSupport.Constructions.supportInclusion X (Purity.Constructions.primeSupport X z) t ∈ Set.range (Scheme.RegularSupport.Constructions.regularInclusion X (Purity.Constructions.primeSupport X z)) := by
      by_contra hn
      apply htG
      rw [Scheme.RegularSupport.Constructions.analyticBoundary_eq]
      exact ⟨⟨t, rfl⟩, hn⟩
    obtain ⟨u, hu⟩ := hreg
    refine ⟨u, ?_⟩
    rw [regularDivisorMap_apply, hu]
    exact ht

omit [Smooth Y.hom] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)] in
include hp in
theorem imageCodimension :
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension (Scheme.RegularSupport.Constructions.regularOver X (Purity.Constructions.primeSupport X z)).hom + (p + 1) =
      Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom := by
  have h := Purity.Constructions.primeRegularDimension_add_one X z
  omega

def localDivisorImmersion : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion (Open.ClosedImmersionComposition.Constructions.ComplexManifold.openManifold (Scheme.ClosedImmersion.Constructions.schemeManifold Y) P.openNeighborhood) (p + 1) :=
  Scheme.OpenImmersion.Constructions.restrictedImmersion (regularDivisorMap i z) P.openNeighborhood (p + 1) (imageCodimension z p hp) (by
    rw [regularDivisorRange i z p hp x P hP]
    exact (Gysin.Constructions.divisorImageOpen i z).isOpen.isClosed_compl.preimage continuous_subtype_val)

theorem localDivisorImmersion_range : Set.range (localDivisorImmersion i z p hp x P hP).regularComplementInclusion =
    Subtype.val ⁻¹' (Gysin.Constructions.divisorImageOpen i z : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))ᶜ :=
  (Scheme.OpenImmersion.Constructions.restrictedMap_range (regularDivisorMap i z) P.openNeighborhood).trans (regularDivisorRange i z p hp x P hP)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.ImageImmersion.Constructions
