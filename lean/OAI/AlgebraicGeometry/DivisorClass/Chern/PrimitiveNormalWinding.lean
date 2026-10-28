import OAI.AlgebraicGeometry.DivisorClass.Chern.IntegralResidueEvaluation
import Mathlib.Algebra.Group.Int.Units

/-! # Primitive Normal Winding -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.PrimitiveNormalWinding

noncomputable section

/-!
# ChernClass: the actual normal winding coefficient is a sign

The explicit positive loop is an integral cycle. It bounds an integral chain
in the contractible normal line. The resulting integral relative class pairs
to one with winding. Together with proved integrality, this shows that the
comparison coefficient with the existing geometric generator is `1` or `-1`.
Choosing between those signs still requires the geometric orientation comparison.
-/

open _root_.CategoryTheory
open scoped Simplicial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- The explicit positive loop, as a cycle in the actual integral singular chains. -/
def positiveLoopIntegralCycle : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains WindingLoop.puncturedPlane) 1 :=
  ⟨AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj WindingLoop.puncturedPlane) WindingLoop.positiveLoopSimplex, by
    rw [AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.mem_chainCycles_iff_succ]
    exact (AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain_boundary (R := ℤ) (TopCat.toSSet.obj WindingLoop.puncturedPlane) (n := 0) WindingLoop.positiveLoopSimplex).trans (by
      let f : Fin 2 → (AlgebraicTopology.Cohomology.Singular.ChainDual.simplicialScalarChains (R := ℤ) (TopCat.toSSet.obj WindingLoop.puncturedPlane)).X 0 :=
        fun i => ((-1 : ℤ) ^ i.val) • AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj WindingLoop.puncturedPlane)
          ((TopCat.toSSet.obj WindingLoop.puncturedPlane).δ i WindingLoop.positiveLoopSimplex)
      exact (Fin.sum_univ_two f).trans (by
        change ((-1 : ℤ) ^ 0) • AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj WindingLoop.puncturedPlane)
            ((TopCat.toSSet.obj WindingLoop.puncturedPlane).δ 0 WindingLoop.positiveLoopSimplex) +
          ((-1 : ℤ) ^ 1) • AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj WindingLoop.puncturedPlane)
            ((TopCat.toSSet.obj WindingLoop.puncturedPlane).δ 1 WindingLoop.positiveLoopSimplex) = 0
        rw [pow_zero, one_zsmul, pow_one, neg_one_zsmul, WindingLoop.positiveLoop_faces_equal, add_neg_cancel]))⟩

/-- Transport the same integral loop through the actual one-coordinate homeomorphism. -/
def normalPositiveLoopCycle : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of NormalWinding.windingNormalPunctured)) 1 :=
  AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map (TopCat.isoOfHomeo NormalWinding.normalPuncturedHomeomorph).inv) 1
    positiveLoopIntegralCycle

/-- The transported actual integral loop has winding exactly one. -/
theorem normalPositiveLoopCycle_winding :
    AlgebraicTopology.Duality.Poincare.RelativeCochainDual.rationalSimplicialChainDualEquiv (TopCat.toSSet.obj (TopCat.of NormalWinding.windingNormalPunctured)) 1
      (WindingSingular.singularWindingCochain (TopCat.of NormalWinding.windingNormalPunctured) NormalWinding.normalPuncturedCoordinate
        NormalWinding.normalPuncturedCoordinate_ne_zero) normalPositiveLoopCycle.val = (1 : ℚ) := by
  have h := LinearMap.congr_fun (AlgebraicTopology.Duality.Poincare.RelativeCochainDual.rationalSimplicialChainDualEquiv_pullback
    (TopCat.toSSet.map (TopCat.isoOfHomeo NormalWinding.normalPuncturedHomeomorph).inv) 1
    (WindingSingular.singularWindingCochain (TopCat.of NormalWinding.windingNormalPunctured) NormalWinding.normalPuncturedCoordinate
      NormalWinding.normalPuncturedCoordinate_ne_zero)) positiveLoopIntegralCycle.val
  have hn := WindingSingular.singularWindingCochain_naturality (TopCat.isoOfHomeo NormalWinding.normalPuncturedHomeomorph).inv
    NormalWinding.normalPuncturedCoordinate NormalWinding.normalPuncturedCoordinate_ne_zero
  change (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) (TopCat.isoOfHomeo NormalWinding.normalPuncturedHomeomorph).inv).f 1
      (WindingSingular.singularWindingCochain (TopCat.of NormalWinding.windingNormalPunctured) NormalWinding.normalPuncturedCoordinate
        NormalWinding.normalPuncturedCoordinate_ne_zero) =
    WindingSingular.singularWindingCochain WindingLoop.puncturedPlane WindingLoop.puncturedCoordinate WindingLoop.puncturedCoordinate_ne_zero at hn
  change AlgebraicTopology.Duality.Poincare.RelativeCochainDual.rationalSimplicialChainDualEquiv (TopCat.toSSet.obj WindingLoop.puncturedPlane) 1
      ((AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) (TopCat.isoOfHomeo NormalWinding.normalPuncturedHomeomorph).inv).f 1
        (WindingSingular.singularWindingCochain (TopCat.of NormalWinding.windingNormalPunctured) NormalWinding.normalPuncturedCoordinate
          NormalWinding.normalPuncturedCoordinate_ne_zero)) positiveLoopIntegralCycle.val =
    AlgebraicTopology.Duality.Poincare.RelativeCochainDual.rationalSimplicialChainDualEquiv (TopCat.toSSet.obj (TopCat.of NormalWinding.windingNormalPunctured)) 1
      (WindingSingular.singularWindingCochain (TopCat.of NormalWinding.windingNormalPunctured) NormalWinding.normalPuncturedCoordinate
        NormalWinding.normalPuncturedCoordinate_ne_zero) normalPositiveLoopCycle.val at h
  rw [hn] at h
  rw [← h]
  change AlgebraicTopology.Duality.Poincare.RelativeCochainDual.rationalSimplicialChainDualEquiv (TopCat.toSSet.obj WindingLoop.puncturedPlane) 1
    (WindingSingular.singularWindingCochain WindingLoop.puncturedPlane WindingLoop.puncturedCoordinate WindingLoop.puncturedCoordinate_ne_zero)
    (AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj WindingLoop.puncturedPlane) WindingLoop.positiveLoopSimplex) = (1 : ℚ)
  rw [AlgebraicTopology.Duality.Poincare.RelativeCochainDual.rationalSimplicialChainDualEquiv_simplex,
    ← AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso_hom_apply, WindingSingular.singularWindingCochain_value, WindingLoop.singularWindingValue_positiveLoop]

/-- The integral loop bounds an integral chain in the actual contractible normal line. -/
theorem exists_normalPositiveLoopFilling :
    ∃ z : (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains NormalWinding.windingNormalLine).X 2,
      (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains NormalWinding.windingNormalLine).d 2 1 z =
        (CycleClass.Geometric.LocalHomology.Cycles.subspaceChainInclusion NormalWinding.windingNormalLine NormalWinding.windingNormalPunctured).f 1 normalPositiveLoopCycle.val := by
  let c := AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap (CycleClass.Geometric.LocalHomology.Cycles.subspaceChainInclusion NormalWinding.windingNormalLine NormalWinding.windingNormalPunctured) 1 normalPositiveLoopCycle
  apply (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass_eq_zero_iff_exists (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains NormalWinding.windingNormalLine) 1 c).mp
  exact @Subsingleton.elim _ (ModuleCat.subsingleton_of_isZero
    (CycleClass.Geometric.ContractibleModel.Cycles.isZero_integralSingularHomology_of_contractible NormalWinding.windingNormalLine 1 (by decide))) _ _

/-- One actual integral filling, used only through its proved boundary. -/
def normalPositiveLoopFilling : (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains NormalWinding.windingNormalLine).X 2 :=
  exists_normalPositiveLoopFilling.choose

theorem normalPositiveLoopFilling_boundary :
    (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains NormalWinding.windingNormalLine).d 2 1 normalPositiveLoopFilling =
      (CycleClass.Geometric.LocalHomology.Cycles.subspaceChainInclusion NormalWinding.windingNormalLine NormalWinding.windingNormalPunctured).f 1 normalPositiveLoopCycle.val :=
  exists_normalPositiveLoopFilling.choose_spec

/-- Its genuine integral relative homology class. -/
def normalPositiveLoopRelativeClass : CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology NormalWinding.windingNormalLine NormalWinding.windingNormalPunctured 2 :=
  AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains NormalWinding.windingNormalLine NormalWinding.windingNormalPunctured) 2
    ⟨(CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection NormalWinding.windingNormalLine NormalWinding.windingNormalPunctured).f 2 normalPositiveLoopFilling,
      IntegralResidueEvaluation.integralRelativeProjection_cycle_of_boundary NormalWinding.windingNormalLine NormalWinding.windingNormalPunctured
        normalPositiveLoopFilling normalPositiveLoopCycle.val normalPositiveLoopFilling_boundary⟩

/-- Actual boundary evaluation proves that this integral relative class pairs to one with winding. -/
theorem normalPositiveLoopRelativeClass_winding :
    AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation NormalWinding.windingNormalLine NormalWinding.windingNormalPunctured 2 NormalWinding.normalSupportedWindingClass
      normalPositiveLoopRelativeClass = 1 :=
  (IntegralResidueEvaluation.supportedWindingClass_integralBoundaryEvaluation NormalWinding.windingNormalLine NormalWinding.windingNormalPunctured
    NormalWinding.normalPuncturedCoordinate NormalWinding.normalPuncturedCoordinate_ne_zero normalPositiveLoopFilling
    normalPositiveLoopCycle.val normalPositiveLoopFilling_boundary).trans normalPositiveLoopCycle_winding

/-- The integral coordinate of that class in the independently constructed normal generator. -/
def normalPositiveLoopCoefficient : ℤ :=
  (CycleClass.Geometric.ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso 1).hom normalPositiveLoopRelativeClass

theorem normalPositiveLoopRelativeClass_coefficient :
    normalPositiveLoopRelativeClass = normalPositiveLoopCoefficient • (CycleClass.Geometric.ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso 1).inv 1 := by
  apply (CycleClass.Geometric.ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso 1).toLinearEquiv.injective
  change (CycleClass.Geometric.ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso 1).hom normalPositiveLoopRelativeClass =
    (CycleClass.Geometric.ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso 1).hom
      (normalPositiveLoopCoefficient • (CycleClass.Geometric.ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso 1).inv 1)
  rw [map_zsmul, Iso.inv_hom_id_apply]
  change normalPositiveLoopCoefficient = normalPositiveLoopCoefficient * 1
  exact (mul_one _).symm

/-- The winding coefficient has an actual integral inverse. -/
theorem normalWindingCoefficient_integral_inverse :
    NormalWinding.normalWindingCoefficient * (normalPositiveLoopCoefficient : ℚ) = 1 := by
  have h := normalPositiveLoopRelativeClass_winding
  rw [normalPositiveLoopRelativeClass_coefficient, map_zsmul,
    NormalWinding.normalSupportedWindingClass_eq_coefficient_smul, map_smul] at h
  change (normalPositiveLoopCoefficient : ℚ) * (NormalWinding.normalWindingCoefficient *
    AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation NormalWinding.windingNormalLine NormalWinding.windingNormalPunctured 2
      (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass 1) ((CycleClass.Geometric.ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso 1).inv 1)) = 1 at h
  rw [AlgebraicTopology.Duality.Poincare.RelativeRationalEvaluationComparison.complexNormalRationalDualClass_integralEvaluation, mul_one] at h
  exact (mul_comm _ _).trans h

/-- The actual geometric comparison factor is a sign, with no assumed orientation agreement. -/
theorem normalWindingCoefficient_eq_one_or_neg_one :
    NormalWinding.normalWindingCoefficient = 1 ∨ NormalWinding.normalWindingCoefficient = -1 := by
  obtain ⟨m, hm⟩ := IntegralResidueEvaluation.normalWindingCoefficient_integral
  have hi : m * normalPositiveLoopCoefficient = 1 := by
    have h := normalWindingCoefficient_integral_inverse
    rw [← hm] at h
    exact_mod_cast h
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hi with h | h
  · left
    rw [← hm, h]
    rfl
  · right
    rw [← hm, h]
    rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.PrimitiveNormalWinding
