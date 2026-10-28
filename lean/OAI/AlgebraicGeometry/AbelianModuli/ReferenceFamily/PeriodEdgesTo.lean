import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SingularPeriodEquiv
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PositiveCohomologyConjugation

/-! # Period Edges To -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PeriodEdgesTo.PeriodEdges

noncomputable section

/-!
# ReferenceFamily: periods as actual singular-edge evaluations

A lifted edge from zero to a lattice vector computes the corresponding period.
This formula also proves compatibility with the project's actual inclusion of
rational cohomology into complex cohomology.
-/

open _root_.CategoryTheory Opposite
open scoped Simplicial

variable {K : Type} [Field K]
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  (Λ : Submodule ℤ V)

/-- The endpoint formula for the normalized primitive computes every period. -/
theorem periodHom_eq_edge_evaluation
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of K K) (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ) 1) (ℓ : Λ)
    (s : AlgebraicTopology.Cohomology.Singular.Basic.singularSimplices (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V)) 1)
    (hs₀ : TopCat.toSSetObj₁Equiv s 0 = 0)
    (hs₁ : TopCat.toSSetObj₁Equiv s 1 = (ℓ : V)) :
    HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.periodHom Λ c ℓ =
      AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ)) (ModuleCat.of K K)
        ((TopCat.toSSet.map (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.projection Λ)).app (op ⦋1⦌) s) c.val := by
  have h := congrArg (fun b =>
    (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))) (ModuleCat.of K K) 1).hom b s)
    (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.primitive_d Λ c)
  rw [AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCoboundary_apply,
    ← TopCat.toSSetObj₁Equiv_apply_one, ← TopCat.toSSetObj₁Equiv_apply_zero,
    hs₀, hs₁] at h
  change HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.primitiveValue Λ c ℓ - HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.primitiveValue Λ c 0 = _ at h
  rw [HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.primitiveValue_zero, sub_zero] at h
  change HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.periodHom Λ c ℓ =
    (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))) (ModuleCat.of K K) 1).hom
      ((AlgebraicTopology.Cohomology.Singular.Functor.simplicialPullback (ModuleCat.of K K)
        (TopCat.toSSet.map (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.projection Λ))).f 1 c.val) s at h
  rw [AlgebraicTopology.Cohomology.Singular.Formulas.degreewiseFunctionIso_pullback, AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso_hom_apply] at h
  exact h

/-- The straight segment from zero to a vector, as an actual singular edge. -/
def vectorEdge (v : V) : AlgebraicTopology.Cohomology.Singular.Basic.singularSimplices (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V)) 1 :=
  TopCat.toSSetObj₁Equiv.symm
    (TopCat.ofHom ((Path.segment (0 : V) v).toContinuousMap.comp
      ⟨TopCat.I.homeomorph, TopCat.I.homeomorph.continuous⟩))

@[simp]
theorem vectorEdge_zero (v : V) : TopCat.toSSetObj₁Equiv (vectorEdge v) 0 = 0 := by
  unfold vectorEdge
  erw [Equiv.apply_symm_apply]
  exact (Path.segment (0 : V) v).source

@[simp]
theorem vectorEdge_one (v : V) : TopCat.toSSetObj₁Equiv (vectorEdge v) 1 = v := by
  unfold vectorEdge
  erw [Equiv.apply_symm_apply]
  exact (Path.segment (0 : V) v).target

/-- Rational coefficient inclusion casts each lattice period to ℂ. -/
theorem cohomologyPeriod_rationalToComplex [DiscreteTopology Λ]
    (u : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ) 1) (ℓ : Λ) :
    HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.cohomologyPeriod (K := ℂ) Λ (AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ) 1 u) ℓ =
      (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.cohomologyPeriod Λ u ℓ : ℂ) := by
  obtain ⟨c, rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.singularClass_surjective (ModuleCat.of ℚ ℚ) (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ) 1 u
  rw [ComplexMultiplication.HodgeComparison.PositiveCohomologyConjugation.CM.Construction.rationalToComplexCohomology_class,
    HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.cohomologyPeriod_class, HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.cohomologyPeriod_class]
  rw [periodHom_eq_edge_evaluation Λ _ ℓ (vectorEdge (ℓ : V))
    (vectorEdge_zero _) (vectorEdge_one _),
    periodHom_eq_edge_evaluation Λ _ ℓ (vectorEdge (ℓ : V))
    (vectorEdge_zero _) (vectorEdge_one _)]
  exact ComplexMultiplication.HodgeComparison.PositiveCohomologyConjugation.CM.Construction.rationalToComplexCochain_evaluation (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ) 1 c.val _

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PeriodEdgesTo.PeriodEdges
