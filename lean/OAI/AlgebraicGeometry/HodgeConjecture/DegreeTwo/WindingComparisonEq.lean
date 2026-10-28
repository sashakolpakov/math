import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CechTransgression
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialCocycleQ
import OAI.AlgebraicGeometry.DivisorClass.Chern.WindingCech

/-! # Winding Comparison Eq -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.WindingComparisonEq.Constructions.WindingComparison

noncomputable section

/-!
# DegreeTwo: logarithm-branch winding versus actual lifted-edge cocycles

The comparison is computed with genuine singular zero-cochains obtained by
applying a rational linear functional to each local logarithm branch.
-/

open _root_.CategoryTheory Opposite _root_.TopologicalSpace
open OAI.AlgebraicGeometry.DivisorClass.Chern.WindingCech.RationalCech

open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialCocycleQ.Constructions.ExponentialCocycle

variable {I : Type} (U : I → Opens ExponentialCocycleQ.Constructions.ExponentialCocycle.Punctured)
variable (F : ℂ →ₗ[ℚ] ℚ) (hF : F (2 * (Real.pi : ℂ) * Complex.I) = 1)
variable (b : DivisorClass.Chern.WindingCech.RationalCech.BranchCochain ExponentialCocycleQ.Constructions.ExponentialCocycle.Punctured U)
variable (hb : ∀ (a : Fin 1 → I) (x : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a),
  Complex.exp (b a x) = x.val.val)

/-- Each continuous branch gives a genuine map to the logarithm plane. -/
def branchMap (a : Fin 1 → I) : TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) ⟶ ExponentialCocycleQ.Constructions.ExponentialCocycle.Plane :=
  TopCat.ofHom (b a)

/-- The corresponding genuine singular zero-cochain on each chart. -/
def branchPrimitive : DivisorClass.Chern.Rational.Cech.RationalCech.CechCochain (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf ExponentialCocycleQ.Constructions.ExponentialCocycle.Q ExponentialCocycleQ.Constructions.ExponentialCocycle.Punctured 0) U 0 :=
  fun a => (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback ExponentialCocycleQ.Constructions.ExponentialCocycle.Q (branchMap U b a)).f 0
    (ExponentialCocycleQ.Constructions.ExponentialCocycle.primitiveZeroCochain F.toAddMonoidHom)

theorem branchPrimitive_precomp_value {n : ℕ} (θ : Fin 1 → Fin (n + 1))
    (a : Fin (n + 1) → I) (x : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) :
    (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso ExponentialCocycleQ.Constructions.ExponentialCocycle.Q (TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a))).hom
      (DivisorClass.Chern.Rational.Cech.RationalCech.cechPrecomp (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf ExponentialCocycleQ.Constructions.ExponentialCocycle.Q ExponentialCocycleQ.Constructions.ExponentialCocycle.Punctured 0) U θ
        (branchPrimitive U F b) a) x =
    F (b (a ∘ θ) ⟨x.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a θ x.property⟩) := by
  change (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso ExponentialCocycleQ.Constructions.ExponentialCocycle.Q (TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a))).hom
      ((AlgebraicTopology.Cohomology.Singular.Functor.singularPullback ExponentialCocycleQ.Constructions.ExponentialCocycle.Q ((Opens.toTopCat ExponentialCocycleQ.Constructions.ExponentialCocycle.Punctured).map
        (homOfLE (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a θ)))).f 0
        ((AlgebraicTopology.Cohomology.Singular.Functor.singularPullback ExponentialCocycleQ.Constructions.ExponentialCocycle.Q (branchMap U b (a ∘ θ))).f 0
          (ExponentialCocycleQ.Constructions.ExponentialCocycle.primitiveZeroCochain F.toAddMonoidHom))) x = _
  erw [AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso_pullback, AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso_pullback,
    PeriodSurjectivityOne.Constructions.PeriodSurjectivity.additiveZeroCochain_value]
  rfl

include hb in
/-- The vertical coboundary is precisely the actual exponential-cover cocycle. -/
theorem branchPrimitive_vertical :
    DivisorClass.Chern.Rational.Cech.RationalCech.cechCoefficientMap U ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex ExponentialCocycleQ.Constructions.ExponentialCocycle.Q ExponentialCocycleQ.Constructions.ExponentialCocycle.Punctured).d 0 1) 0
      (branchPrimitive U F b) =
    (DivisorClass.Chern.Rational.CechComparison.RationalCech.globalSingularCechColumnAugmentation ExponentialCocycleQ.Constructions.ExponentialCocycle.Punctured U ExponentialCocycleQ.Constructions.ExponentialCocycle.Q).f 1
      (ExponentialCocycleQ.Constructions.ExponentialCocycle.cocycle F.toAddMonoidHom).val := by
  funext a
  rw [DivisorClass.Chern.Rational.CechComparison.RationalCech.globalSingularCechColumnAugmentation_apply]
  exact ExponentialCocycleQ.Constructions.ExponentialCocycle.localPrimitive F.toAddMonoidHom
    (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩) (branchMap U b a)
    (by
      apply TopCat.ext
      intro x
      apply Subtype.ext
      exact hb a x)

include hF in
/-- Applying the normalized rational functional to a branch difference reads
 exactly its already constructed rational exponential period. -/
theorem branchWindingCech_eq_functional (h : DivisorClass.Chern.WindingCech.RationalCech.BranchCompatibility ExponentialCocycleQ.Constructions.ExponentialCocycle.Punctured U b)
    (a : Fin 2 → I) (x : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) :
    DivisorClass.Chern.WindingCech.RationalCech.branchWindingCech ExponentialCocycleQ.Constructions.ExponentialCocycle.Punctured U b h a x =
      F (DivisorClass.Chern.Rational.Cech.RationalCech.cechDelta (DivisorClass.Chern.LogCech.RationalCech.continuousComplexPresheaf ExponentialCocycleQ.Constructions.ExponentialCocycle.Punctured) U 0 b a x) := by
  have hp := congrArg (fun c : DivisorClass.Chern.Rational.Cech.RationalCech.CechCochain (DivisorClass.Chern.LogCech.RationalCech.continuousComplexPresheaf ExponentialCocycleQ.Constructions.ExponentialCocycle.Punctured) U 1 => c a x)
    (DivisorClass.Chern.WindingCech.RationalCech.periodMap_branchWindingCech ExponentialCocycleQ.Constructions.ExponentialCocycle.Punctured U b h)
  change (DivisorClass.Chern.WindingCech.RationalCech.branchWindingCech ExponentialCocycleQ.Constructions.ExponentialCocycle.Punctured U b h a x : ℚ) •
      (2 * (Real.pi : ℂ) * Complex.I) = _ at hp
  have he := congrArg F hp
  rw [map_smul, hF, smul_eq_mul, mul_one] at he
  exact he

include hF in
/-- Horizontal differences of the local singular primitives are the actual
 locally constant winding cocycle. -/
theorem branchPrimitive_horizontal (h : DivisorClass.Chern.WindingCech.RationalCech.BranchCompatibility ExponentialCocycleQ.Constructions.ExponentialCocycle.Punctured U b) :
    DivisorClass.Chern.Rational.Cech.RationalCech.cechDelta (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf ExponentialCocycleQ.Constructions.ExponentialCocycle.Q ExponentialCocycleQ.Constructions.ExponentialCocycle.Punctured 0) U 0 (branchPrimitive U F b) =
      DivisorClass.Chern.Cech.Obj.RationalCech.locallyConstantCechEvaluation ExponentialCocycleQ.Constructions.ExponentialCocycle.Punctured U 1 (DivisorClass.Chern.WindingCech.RationalCech.branchWindingCocycle ExponentialCocycleQ.Constructions.ExponentialCocycle.Punctured U b h).val := by
  funext a
  apply (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso ExponentialCocycleQ.Constructions.ExponentialCocycle.Q (TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a))).toLinearEquiv.injective
  ext x
  rw [DivisorClass.Chern.Rational.Cech.RationalCech.cechDelta_apply, Fin.sum_univ_two]
  change (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso ExponentialCocycleQ.Constructions.ExponentialCocycle.Q (TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a))).hom
      ((1 : ℤ) • DivisorClass.Chern.Rational.Cech.RationalCech.cechPrecomp (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf ExponentialCocycleQ.Constructions.ExponentialCocycle.Q ExponentialCocycleQ.Constructions.ExponentialCocycle.Punctured 0) U
          (0 : Fin 2).succAbove (branchPrimitive U F b) a +
        (-1 : ℤ) • DivisorClass.Chern.Rational.Cech.RationalCech.cechPrecomp (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf ExponentialCocycleQ.Constructions.ExponentialCocycle.Q ExponentialCocycleQ.Constructions.ExponentialCocycle.Punctured 0) U
          (1 : Fin 2).succAbove (branchPrimitive U F b) a) x =
    (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso ExponentialCocycleQ.Constructions.ExponentialCocycle.Q (TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a))).hom
      (AlgebraicTopology.Cohomology.Singular.Augmentation.locallyConstantToSingularZero ExponentialCocycleQ.Constructions.ExponentialCocycle.Q (TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a))
        (DivisorClass.Chern.WindingCech.RationalCech.branchWindingCech ExponentialCocycleQ.Constructions.ExponentialCocycle.Punctured U b h a)) x
  erw [one_zsmul, neg_one_zsmul, ← sub_eq_add_neg, map_sub]
  change (_ : ℚ) - _ = _
  rw [branchPrimitive_precomp_value, branchPrimitive_precomp_value,
    AlgebraicTopology.Cohomology.Singular.Augmentation.locallyConstantToSingularZero_apply, branchWindingCech_eq_functional U F hF]
  rw [DivisorClass.Chern.Rational.Cech.RationalCech.cechDelta_apply, Fin.sum_univ_two]
  change F _ - F _ = F ((1 : ℤ) • _ + (-1 : ℤ) • _)
  rw [one_zsmul, neg_one_zsmul, ← sub_eq_add_neg, map_sub]
  rfl

include hF hb in
/-- The existing logarithm-branch construction is the negative of the
 actual lifted-edge singular class for this total-complex convention. -/
theorem branchWindingClass_eq_neg_exponentialClass
    (hU : ∀ x : ExponentialCocycleQ.Constructions.ExponentialCocycle.Punctured, ∃ i, x ∈ U i) (h : DivisorClass.Chern.WindingCech.RationalCech.BranchCompatibility ExponentialCocycleQ.Constructions.ExponentialCocycle.Punctured U b) :
    DivisorClass.Chern.WindingCech.RationalCech.branchWindingClass ExponentialCocycleQ.Constructions.ExponentialCocycle.Punctured U hU b h =
      -AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains ExponentialCocycleQ.Constructions.ExponentialCocycle.Q ExponentialCocycleQ.Constructions.ExponentialCocycle.Punctured) 1 (ExponentialCocycleQ.Constructions.ExponentialCocycle.cocycle F.toAddMonoidHom) :=
  CechTransgression.Constructions.cechClass_eq_neg_singularClass_of_primitives ExponentialCocycleQ.Constructions.ExponentialCocycle.Punctured U hU (ExponentialCocycleQ.Constructions.ExponentialCocycle.cocycle F.toAddMonoidHom)
    (DivisorClass.Chern.WindingCech.RationalCech.branchWindingCocycle ExponentialCocycleQ.Constructions.ExponentialCocycle.Punctured U b h) (branchPrimitive U F b)
    (branchPrimitive_vertical U F b hb) (branchPrimitive_horizontal U F hF b h)

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.WindingComparisonEq.Constructions.WindingComparison
