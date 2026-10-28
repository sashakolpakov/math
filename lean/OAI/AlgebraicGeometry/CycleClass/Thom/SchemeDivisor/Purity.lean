import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport
import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.CodimensionTwoRemoval
import OAI.AlgebraicGeometry.DivisorClass.Chern.SupportCodimension

/-! # Purity -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Purity.Constructions

noncomputable section

/-! A prime divisor's actual singular boundary has ambient codimension at least
two, and its regular analytic locus has exactly codimension one. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [LocallyOfFiniteType X.hom]
  (z : {x : X.left // Order.coheight x = 1})

abbrev primeSupport : IrreducibleCloseds X.left := irreducibleSetEquivPoints.symm z.val

def primeSingularBoundary : Closeds X.left :=
  ⟨Geometric.StratumDimension.supportSingularBoundary (primeSupport X z) X.hom,
    Geometric.StratumDimension.isClosed_supportSingularBoundary (primeSupport X z) X.hom⟩

omit [IsIntegral X.left] in
theorem primeSingularBoundary_coheight (y : X.left) (hy : y ∈ primeSingularBoundary X z) :
    1 < Order.coheight y := by
  let Y : IrreducibleCloseds X.left := irreducibleSetEquivPoints.symm y
  have hY : (Y : Set X.left) ⊆ Geometric.StratumDimension.supportSingularBoundary (primeSupport X z) X.hom :=
    closure_minimal (Set.singleton_subset_iff.mpr hy)
      (Geometric.StratumDimension.isClosed_supportSingularBoundary (primeSupport X z) X.hom)
  have hlt := Geometric.StratumDimension.lt_of_subset_supportSingularBoundary Y (primeSupport X z) X.hom hY
  have hc := Order.coheight_add_one_le hlt
  have hz : Order.coheight (primeSupport X z) = 1 := by
    simpa only [primeSupport, Order.coheight_orderIso] using z.property
  rw [hz] at hc
  have hYc : Order.coheight Y = Order.coheight y := by
    simp only [Y, Order.coheight_orderIso]
  rw [hYc] at hc
  exact lt_of_lt_of_le (by decide : (1 : ℕ∞) < 1 + 1) hc

theorem primeRegularDimension_add_one :
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension (Scheme.RegularSupport.Constructions.regularOver X (primeSupport X z)).hom + 1 =
      Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom := by
  rw [Scheme.RegularSupport.Constructions.regularDimension_eq]
  exact (DivisorClass.Chern.SupportCodimension.Construction.pointClosure_dimension_add_one X.hom z.val z.property).trans
    (Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension X.hom)

omit [IsIntegral X.left] in
theorem primeSupportComplement_subset_regularAmbient :
    (Set.range (Scheme.RegularSupport.Constructions.supportInclusion X (primeSupport X z)))ᶜ ⊆ Scheme.RegularSupport.Constructions.regularAmbientOpen X (primeSupport X z) := by
  intro y hy hboundary
  rw [Scheme.RegularSupport.Constructions.analyticBoundary_eq] at hboundary
  exact hy hboundary.1

variable [Smooth X.hom] [AlgebraicGeometry.IsNoetherian X.left]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]

theorem primeRegularRestriction_isIso :
    IsIso (Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
      (Set.range (Scheme.RegularSupport.Constructions.supportInclusion X (primeSupport X z)))ᶜ
      (Scheme.RegularSupport.Constructions.regularAmbientOpen X (primeSupport X z)) 2) :=
  Scheme.CodimensionTwoRemoval.Constructions.codimensionTwo_relativeRestriction_isIso X
    (primeSingularBoundary X z) (primeSingularBoundary_coheight X z)
    (Set.range (Scheme.RegularSupport.Constructions.supportInclusion X (primeSupport X z)))ᶜ
    (primeSupportComplement_subset_regularAmbient X z)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Purity.Constructions
