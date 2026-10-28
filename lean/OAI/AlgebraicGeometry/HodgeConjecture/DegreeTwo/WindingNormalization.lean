import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.WindingComparisonEq
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.PeriodEdges
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LoopEvaluationEq

/-! # Winding Normalization -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.WindingNormalization.Constructions.ExponentialCocycle

noncomputable section

/-!
# DegreeTwo: a nonzero winding class with its actual singular-loop normalization

The lifted-edge cocycle evaluates to one on the positive exponential loop.
The existing Cech comparison therefore gives value minus one for its
logarithm-branch winding class. In particular that class is not zero.
-/

open _root_.CategoryTheory Opposite
open scoped Simplicial

/-- The actual positive exponential loop, lifted by the straight segment to `2πi`. -/
def standardLoop : AlgebraicTopology.Cohomology.Singular.Basic.singularSimplices ExponentialCocycleQ.Constructions.ExponentialCocycle.Punctured 1 :=
  (TopCat.toSSet.map ExponentialCocycleQ.Constructions.ExponentialCocycle.exponentialMap).app (op ⦋1⦌)
    (PeriodEdges.Constructions.SingularPeriods.vectorEdge (2 * (Real.pi : ℂ) * Complex.I))

theorem standardLoop_closed :
    (TopCat.toSSet.obj ExponentialCocycleQ.Constructions.ExponentialCocycle.Punctured).δ 0 standardLoop =
      (TopCat.toSSet.obj ExponentialCocycleQ.Constructions.ExponentialCocycle.Punctured).δ 1 standardLoop := by
  apply TopCat.toSSetObj₀Equiv.injective
  erw [← TopCat.toSSetObj₁Equiv_apply_one, ← TopCat.toSSetObj₁Equiv_apply_zero]
  change ExponentialCocycleQ.Constructions.ExponentialCocycle.exponentialMap (TopCat.toSSetObj₁Equiv
      (PeriodEdges.Constructions.SingularPeriods.vectorEdge (2 * (Real.pi : ℂ) * Complex.I)) 1) =
    ExponentialCocycleQ.Constructions.ExponentialCocycle.exponentialMap (TopCat.toSSetObj₁Equiv
      (PeriodEdges.Constructions.SingularPeriods.vectorEdge (2 * (Real.pi : ℂ) * Complex.I)) 0)
  rw [PeriodEdges.Constructions.SingularPeriods.vectorEdge_one, PeriodEdges.Constructions.SingularPeriods.vectorEdge_zero]
  apply Subtype.ext
  exact Complex.exp_two_pi_mul_I.trans Complex.exp_zero.symm

variable (F : ℂ →ₗ[ℚ] ℚ) (hF : F (2 * (Real.pi : ℂ) * Complex.I) = 1)

include hF in
/-- The genuine lifted-edge cocycle has value one on this explicit singular loop. -/
theorem standardLoop_cocycle_evaluation :
    AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj ExponentialCocycleQ.Constructions.ExponentialCocycle.Punctured) ExponentialCocycleQ.Constructions.ExponentialCocycle.Q standardLoop
      (ExponentialCocycleQ.Constructions.ExponentialCocycle.cocycle F.toAddMonoidHom).val = 1 := by
  let s := PeriodEdges.Constructions.SingularPeriods.vectorEdge (2 * (Real.pi : ℂ) * Complex.I)
  have h := congrArg (fun c => (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj ExponentialCocycleQ.Constructions.ExponentialCocycle.Plane) ExponentialCocycleQ.Constructions.ExponentialCocycle.Q 1).hom c s)
    (ExponentialCocycleQ.Constructions.ExponentialCocycle.oneCochain_pullback F.toAddMonoidHom)
  change (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj ExponentialCocycleQ.Constructions.ExponentialCocycle.Plane) ExponentialCocycleQ.Constructions.ExponentialCocycle.Q 1).hom
      ((AlgebraicTopology.Cohomology.Singular.Functor.simplicialPullback ExponentialCocycleQ.Constructions.ExponentialCocycle.Q (TopCat.toSSet.map ExponentialCocycleQ.Constructions.ExponentialCocycle.exponentialMap)).f 1 (ExponentialCocycleQ.Constructions.ExponentialCocycle.oneCochain F.toAddMonoidHom)) s = _ at h
  rw [AlgebraicTopology.Cohomology.Singular.Formulas.degreewiseFunctionIso_pullback, AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso_hom_apply,
    PeriodSurjectivityOne.Constructions.PeriodSurjectivity.additiveCoboundary_apply] at h
  change AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj ExponentialCocycleQ.Constructions.ExponentialCocycle.Punctured) ExponentialCocycleQ.Constructions.ExponentialCocycle.Q standardLoop
      (ExponentialCocycleQ.Constructions.ExponentialCocycle.cocycle F.toAddMonoidHom).val =
    F (TopCat.toSSetObj₁Equiv s 1) - F (TopCat.toSSetObj₁Equiv s 0) at h
  rw [PeriodEdges.Constructions.SingularPeriods.vectorEdge_one, PeriodEdges.Constructions.SingularPeriods.vectorEdge_zero, map_zero, sub_zero, hF] at h
  exact h

include hF in
/-- Its cohomology class is nonzero because coboundaries vanish on this loop. -/
theorem cocycle_class_ne_zero :
    AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains ExponentialCocycleQ.Constructions.ExponentialCocycle.Q ExponentialCocycleQ.Constructions.ExponentialCocycle.Punctured) 1 (ExponentialCocycleQ.Constructions.ExponentialCocycle.cocycle F.toAddMonoidHom) ≠ 0 := by
  intro hz
  have he := LoopEvaluationEq.Constructions.LoopEvaluation.cocycle_evaluation_eq (TopCat.toSSet.obj ExponentialCocycleQ.Constructions.ExponentialCocycle.Punctured) ExponentialCocycleQ.Constructions.ExponentialCocycle.Q
    (ExponentialCocycleQ.Constructions.ExponentialCocycle.cocycle F.toAddMonoidHom) 0 (by simpa only [map_zero] using hz)
    standardLoop standardLoop_closed
  rw [standardLoop_cocycle_evaluation F hF] at he
  change (1 : ℚ) = AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj ExponentialCocycleQ.Constructions.ExponentialCocycle.Punctured) ExponentialCocycleQ.Constructions.ExponentialCocycle.Q standardLoop 0 at he
  rw [map_zero] at he
  exact one_ne_zero he

/-- The tautological nonvanishing function on the punctured plane. -/
def tautologicalFunction : C(ExponentialCocycleQ.Constructions.ExponentialCocycle.Punctured, ℂ) := ⟨Subtype.val, continuous_subtype_val⟩

/-- The already constructed logarithm-branch winding class of the coordinate function. -/
def universalWindingClass := DivisorClass.Chern.WindingCech.RationalCech.logarithmicWindingClass ExponentialCocycleQ.Constructions.ExponentialCocycle.Punctured tautologicalFunction
  (fun z => z.property)

include hF in
theorem universalWindingClass_eq :
    universalWindingClass = -AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains ExponentialCocycleQ.Constructions.ExponentialCocycle.Q ExponentialCocycleQ.Constructions.ExponentialCocycle.Punctured) 1
      (ExponentialCocycleQ.Constructions.ExponentialCocycle.cocycle F.toAddMonoidHom) :=
  WindingComparisonEq.Constructions.WindingComparison.branchWindingClass_eq_neg_exponentialClass
    (DivisorClass.Chern.WindingCech.RationalCech.functionLogCover ExponentialCocycleQ.Constructions.ExponentialCocycle.Punctured tautologicalFunction) F hF
    (DivisorClass.Chern.WindingCech.RationalCech.functionLogBranches ExponentialCocycleQ.Constructions.ExponentialCocycle.Punctured tautologicalFunction)
    (DivisorClass.Chern.WindingCech.RationalCech.functionLogBranches_exp ExponentialCocycleQ.Constructions.ExponentialCocycle.Punctured tautologicalFunction (fun z => z.property))
    (DivisorClass.Chern.WindingCech.RationalCech.functionLogCover_covers ExponentialCocycleQ.Constructions.ExponentialCocycle.Punctured tautologicalFunction (fun z => z.property))
    (DivisorClass.Chern.WindingCech.RationalCech.functionLogBranches_compatible ExponentialCocycleQ.Constructions.ExponentialCocycle.Punctured tautologicalFunction (fun z => z.property))

omit F hF in
/-- A rational linear functional normalized on the actual nonzero exponential period exists. -/
theorem exists_normalizedFunctional :
    ∃ F : ℂ →ₗ[ℚ] ℚ, F (2 * (Real.pi : ℂ) * Complex.I) = 1 :=
  Module.Projective.exists_dual_eq_one ℚ Complex.two_pi_I_ne_zero

omit F hF in
/-- The actual logarithm-branch winding construction gives a nonzero rational class. -/
theorem universalWindingClass_ne_zero : universalWindingClass ≠ 0 := by
  obtain ⟨F, hF⟩ := exists_normalizedFunctional
  rw [universalWindingClass_eq F hF, neg_ne_zero]
  exact cocycle_class_ne_zero F hF

/-- Any genuine singular cocycle representing the logarithm-branch winding class
 evaluates to minus one on the actual positive exponential loop. -/
theorem universalWindingClass_loop_evaluation
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains ExponentialCocycleQ.Constructions.ExponentialCocycle.Q ExponentialCocycleQ.Constructions.ExponentialCocycle.Punctured) 1)
    (hc : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains ExponentialCocycleQ.Constructions.ExponentialCocycle.Q ExponentialCocycleQ.Constructions.ExponentialCocycle.Punctured) 1 c = universalWindingClass) :
    AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj ExponentialCocycleQ.Constructions.ExponentialCocycle.Punctured) ExponentialCocycleQ.Constructions.ExponentialCocycle.Q standardLoop c.val = -1 := by
  obtain ⟨F, hF⟩ := exists_normalizedFunctional
  have he := LoopEvaluationEq.Constructions.LoopEvaluation.cocycle_evaluation_eq (TopCat.toSSet.obj ExponentialCocycleQ.Constructions.ExponentialCocycle.Punctured) ExponentialCocycleQ.Constructions.ExponentialCocycle.Q
    c (-(ExponentialCocycleQ.Constructions.ExponentialCocycle.cocycle F.toAddMonoidHom))
    (by rw [map_neg, hc, universalWindingClass_eq F hF]) standardLoop standardLoop_closed
  change _ = AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj ExponentialCocycleQ.Constructions.ExponentialCocycle.Punctured) ExponentialCocycleQ.Constructions.ExponentialCocycle.Q standardLoop
    (-(ExponentialCocycleQ.Constructions.ExponentialCocycle.cocycle F.toAddMonoidHom).val) at he
  rw [map_neg, standardLoop_cocycle_evaluation F hF] at he
  exact he

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.WindingNormalization.Constructions.ExponentialCocycle
