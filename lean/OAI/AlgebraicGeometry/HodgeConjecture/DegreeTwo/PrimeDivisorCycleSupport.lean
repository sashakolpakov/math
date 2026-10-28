import OAI.AlgebraicGeometry.DivisorClass.Chern.SupportCodimension
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SectionPrimeSupport
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SupportRegularBoundary

/-! # Prime Divisor Cycle Support -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.PrimeDivisorCycleSupport.Constructions

noncomputable section

/-!
# DegreeTwo: actual prime divisors in the target cycle-support grading

The codimension-one point determines the actual reduced closed cycle
support. The proved section zero-locus identification agrees with the
image of that support's actual analytic inclusion.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

/-- An actual codimension-one point as a support in the target variety's
existing dimension-graded cycle group. -/
def primeDivisorCycleSupport (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (z : {z : V.carrier // Order.coheight z = 1}) : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1 := by
  refine ⟨irreducibleSetEquivPoints.symm z.val, ?_⟩
  have hd := DivisorClass.Chern.SupportCodimension.Construction.pointClosure_dimension_add_one V.structureMap z.val z.property
  change Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension V.structureMap -
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm z.val) V.structureMap = 1
  omega

theorem primeDivisorCycleSupport_range (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (z : {z : V.carrier // Order.coheight z = 1}) :
    Set.range (primeDivisorCycleSupport V z).analyticInclusion =
      V.analyticUnderlying ⁻¹' closure ({z.val} : Set V.carrier) := by
  rw [CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.range_analyticInclusion]
  rfl

/-- The actual regular parameter cuts out the actual analytic image of
the prime divisor in the cycle group, on a principal neighborhood. -/
theorem section_uniformizer_primeCycleSupport_neighborhood (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (U : V.carrier.Opens) (hU : IsAffineOpen U)
    (z : {z : V.carrier // Order.coheight z = 1}) (hzU : z.val ∈ U)
    (p : Γ(V.carrier, U)) (hp : Irreducible (V.carrier.presheaf.germ U z.val hzU p)) :
    ∃ b : Γ(V.carrier, U), IsUnit (V.carrier.presheaf.germ U z.val hzU b) ∧
      ∀ y : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation U, DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn V.presentation U b y ≠ 0 →
        (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn V.presentation U p y = 0 ↔
          y.val ∈ Set.range (primeDivisorCycleSupport V z).analyticInclusion) := by
  obtain ⟨b, hb, hs⟩ := SectionPrimeSupport.Constructions.section_uniformizer_prime_support_neighborhood
    V.presentation U hU z.val hzU z.property p hp
  refine ⟨b, hb, ?_⟩
  intro y hy
  rw [primeDivisorCycleSupport_range]
  exact hs y hy

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.PrimeDivisorCycleSupport.Constructions
