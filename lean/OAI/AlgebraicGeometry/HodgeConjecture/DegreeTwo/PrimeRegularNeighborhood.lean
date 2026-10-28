import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.PrimeDivisorCycleSupport
import OAI.AlgebraicGeometry.DivisorClass.Chern.AnalyticUniformizerSupport
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.RegularLocusComplement

/-! # Prime Regular Neighborhood -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.PrimeRegularNeighborhood.Constructions

noncomputable section

/-!
# DegreeTwo: a genuine algebraic open for the regular divisor comparison

The principal denominator is a unit at the actual prime-divisor point.
Intersecting its basic open with the complement of the actual singular
boundary preserves that point and enforces every analytic prerequisite.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem exists_prime_regular_neighborhood (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (z : {z : V.carrier // Order.coheight z = 1})
    (U : V.carrier.Opens) (hU : IsAffineOpen U) (hzU : z.val ∈ U)
    (b : Γ(V.carrier, U)) (hb : IsUnit (V.carrier.presheaf.germ U z.val hzU b)) :
    ∃ (W : V.carrier.Opens), z.val ∈ W ∧
      ∃ hWU : W ≤ U,
        ∀ y : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation W,
          y.val ∈ (PrimeDivisorCycleSupport.Constructions.primeDivisorCycleSupport V z).regularAmbientOpen ∧
          DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn V.presentation U b ⟨y.val, hWU y.property⟩ ≠ 0 := by
  let : Smooth V.structureMap := V.presentation.smooth
  let Z := PrimeDivisorCycleSupport.Constructions.primeDivisorCycleSupport V z
  let R : V.carrier.Opens :=
    ⟨(CycleClass.Geometric.StratumDimension.supportSingularBoundary Z.val V.structureMap)ᶜ,
      (CycleClass.Geometric.StratumDimension.isClosed_supportSingularBoundary Z.val V.structureMap).isOpen_compl⟩
  have hzR : z.val ∈ R := by
    have h := CycleClass.Geometric.StratumDimension.genericPoint_not_mem_supportSingularBoundary Z.val V.structureMap
    have he : irreducibleSetEquivPoints Z.val = z.val :=
      irreducibleSetEquivPoints.apply_symm_apply z.val
    rwa [he] at h
  let W := V.carrier.basicOpen b ⊓ R
  have hWU : W ≤ U := inf_le_left.trans (V.carrier.basicOpen_le b)
  refine ⟨W, ⟨(V.carrier.mem_basicOpen b z.val hzU).mpr hb, hzR⟩, hWU, ?_⟩
  intro y
  refine ⟨y.property.2, ?_⟩
  intro hy
  have hn := (DivisorClass.Chern.AnalyticUniformizerSupport.sectionEvaluationOn_zero_iff_nonunit
    V.presentation U hU b ⟨y.val, hWU y.property⟩).mp hy
  exact hn ((V.carrier.mem_basicOpen b (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying y.val)
    (hWU y.property)).mp y.property.1)

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.PrimeRegularNeighborhood.Constructions
