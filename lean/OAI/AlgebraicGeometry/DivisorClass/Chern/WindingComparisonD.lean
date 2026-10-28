import OAI.AlgebraicGeometry.DivisorClass.Chern.WindingCech
import OAI.AlgebraicGeometry.DivisorClass.Chern.WindingSingular

/-! # Winding Comparison D -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.WindingComparisonD

noncomputable section

/-!
# ChernClass: comparing logarithmic Cech winding with singular path winding

The integral pointwise differences from the principal logarithm form a degree
zero element of the actual singular Cech double complex. Its two differentials
are the Cech winding cocycle and the restricted singular winding cocycle.
This supplies an explicit comparison and fixes its totalization sign.
-/

open _root_.CategoryTheory _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace RationalCech

variable {I : Type} (X : TopCat.{0}) (U : I → Opens X)
variable (g : C(X, ℂ)) (hg : ∀ x, g x ≠ 0) (b : WindingCech.RationalCech.BranchCochain X U)
variable (hb : ∀ a x, Complex.exp (b a x) = g x.val)

/-- The actual zero-cochain primitives of the local logarithm branches. -/
def branchPointPrimitives : Rational.Cech.RationalCech.CechCochain (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf (ModuleCat.of ℚ ℚ) X 0) U 0 :=
  fun a => WindingSingular.pointLogPrimitive (TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a))
    (g.comp ⟨Subtype.val, continuous_subtype_val⟩) (fun x => hg x.val) (b a) (hb a)

/-- Its vertical differential is the genuine restriction of the singular winding cochain. -/
theorem branchPointPrimitives_vertical :
    Rational.Cech.RationalCech.cechCoefficientMap U ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).d 0 1) 0
      (branchPointPrimitives X U g hg b hb) =
    (Rational.CechComparison.RationalCech.globalSingularCechColumnAugmentation X U (ModuleCat.of ℚ ℚ)).f 1
      (WindingSingular.singularWindingCochain X g hg) := by
  funext a
  rw [Rational.CechComparison.RationalCech.globalSingularCechColumnAugmentation_apply]
  change (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) (TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a))).d 0 1
      (WindingSingular.pointLogPrimitive (TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a))
        (g.comp ⟨Subtype.val, continuous_subtype_val⟩) (fun x => hg x.val) (b a) (hb a)) = _
  rw [WindingSingular.pointLogPrimitive_d]
  exact (WindingSingular.singularWindingCochain_naturality
    (show TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) ⟶ X from TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)
    g hg).symm

/-- Its horizontal differential is the evaluated integral branch-difference cocycle. -/
theorem branchPointPrimitives_horizontal :
    Rational.Cech.RationalCech.cechDelta (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf (ModuleCat.of ℚ ℚ) X 0) U 0
      (branchPointPrimitives X U g hg b hb) =
    Cech.Obj.RationalCech.locallyConstantCechEvaluation X U 1
      (WindingCech.RationalCech.branchWindingCech X U b (WindingCech.RationalCech.branchCompatibility_of_global X U g hg b hb)) := by
  funext a
  apply (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso (ModuleCat.of ℚ ℚ)
    (TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a))).toLinearEquiv.injective
  change (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso (ModuleCat.of ℚ ℚ)
    (TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a))).hom _ =
    (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso (ModuleCat.of ℚ ℚ)
    (TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a))).hom _
  ext x
  rw [Rational.Cech.RationalCech.cechDelta_apply, Fin.sum_univ_two]
  change (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso (ModuleCat.of ℚ ℚ) (TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a))).hom
    ((1 : ℤ) • (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ)
      (TopCat.ofHom (LogRefinementOpen.Construction.openInclusionMap (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a (0 : Fin 2).succAbove)))).f 0
        (branchPointPrimitives X U g hg b hb (a ∘ (0 : Fin 2).succAbove)) +
      (-1 : ℤ) • (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ)
      (TopCat.ofHom (LogRefinementOpen.Construction.openInclusionMap (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a (1 : Fin 2).succAbove)))).f 0
        (branchPointPrimitives X U g hg b hb (a ∘ (1 : Fin 2).succAbove))) x =
    (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso (ModuleCat.of ℚ ℚ) (TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a))).hom
      (AlgebraicTopology.Cohomology.Singular.Augmentation.locallyConstantToSingularZero (ModuleCat.of ℚ ℚ) (TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a))
        (WindingCech.RationalCech.branchWindingCech X U b (WindingCech.RationalCech.branchCompatibility_of_global X U g hg b hb) a)) x
  rw [one_zsmul, neg_one_zsmul, map_add, map_neg]
  dsimp only [Pi.add_apply, Pi.neg_apply]
  unfold branchPointPrimitives
  rw [AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso_pullback, AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso_pullback,
    AlgebraicTopology.Cohomology.Singular.Augmentation.locallyConstantToSingularZero_apply]
  change (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso (ModuleCat.of ℚ ℚ) _).hom (WindingSingular.pointLogPrimitive _ _ _ _ _) _ +
    -(AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso (ModuleCat.of ℚ ℚ) _).hom (WindingSingular.pointLogPrimitive _ _ _ _ _) _ = _
  rw [WindingSingular.pointLogPrimitive_value, WindingSingular.pointLogPrimitive_value]
  apply (Rat.cast_injective (α := ℂ))
  apply mul_right_cancel₀ Complex.two_pi_I_ne_zero
  push_cast
  rw [add_mul, neg_mul, WindingSingular.pointLogPeriod_spec, WindingSingular.pointLogPeriod_spec]
  have h := congrArg (fun c : Rational.Cech.RationalCech.CechCochain (LogCech.RationalCech.continuousComplexPresheaf X) U 1 => c a x)
    (WindingCech.RationalCech.periodMap_branchWindingCech X U b (WindingCech.RationalCech.branchCompatibility_of_global X U g hg b hb))
  change ((WindingCech.RationalCech.branchWindingCech X U b (WindingCech.RationalCech.branchCompatibility_of_global X U g hg b hb) a x : ℚ) : ℂ) *
    (2 * (Real.pi : ℂ) * Complex.I) = Rational.Cech.RationalCech.cechDelta (LogCech.RationalCech.continuousComplexPresheaf X) U 0 b a x at h
  rw [h, Rational.Cech.RationalCech.cechDelta_apply, Fin.sum_univ_two]
  change (b (a ∘ (0 : Fin 2).succAbove) _ - Complex.log (g x.val)) +
    -(b (a ∘ (1 : Fin 2).succAbove) _ - Complex.log (g x.val)) =
    (1 : ℤ) • b (a ∘ (0 : Fin 2).succAbove) _ +
      (-1 : ℤ) • b (a ∘ (1 : Fin 2).succAbove) _
  rw [one_zsmul, neg_one_zsmul]
  ring_nf
  rfl

/-- The degree-zero total primitive compares the two actual degree-one cocycles. -/
theorem branchPointPrimitives_total_d :
    (Rational.CechComparison.RationalCech.singularCechTotal X U (ModuleCat.of ℚ ℚ)).d 0 1
      (Rational.Cech.RationalCech.cechTotalInclusion U (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X) 0 0 0 rfl
        (branchPointPrimitives X U g hg b hb)) =
    (Cech.Obj.RationalCech.locallyConstantCechToTotal X U).f 1
        (WindingCech.RationalCech.branchWindingCech X U b (WindingCech.RationalCech.branchCompatibility_of_global X U g hg b hb)) +
      (Rational.CechComparison.RationalCech.globalSingularCechAugmentation X U (ModuleCat.of ℚ ℚ)).f 1
        (WindingSingular.singularWindingCochain X g hg) := by
  have h := ConcreteCategory.congr_hom
    (Rational.Cech.RationalCech.cechTotalInclusion_d U (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X) 0 0 0 rfl)
    (branchPointPrimitives X U g hg b hb)
  change (Rational.CechComparison.RationalCech.singularCechTotal X U (ModuleCat.of ℚ ℚ)).d 0 1
      (Rational.Cech.RationalCech.cechTotalInclusion U (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X) 0 0 0 rfl
        (branchPointPrimitives X U g hg b hb)) =
    Rational.Cech.RationalCech.cechTotalInclusion U (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X) 1 0 1 rfl
      (Rational.Cech.RationalCech.cechDelta (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf (ModuleCat.of ℚ ℚ) X 0) U 0
        (branchPointPrimitives X U g hg b hb)) +
    (1 : ℤ) • Rational.Cech.RationalCech.cechTotalInclusion U (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X) 0 1 1 rfl
      (Rational.Cech.RationalCech.cechCoefficientMap U ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).d 0 1) 0
        (branchPointPrimitives X U g hg b hb)) at h
  rw [branchPointPrimitives_horizontal, branchPointPrimitives_vertical, one_zsmul] at h
  exact h

/-- With the actual total-complex signs, Cech branch winding is the negative
of the singular winding measured by increasing logarithm along a path. -/
theorem branchWindingClass_eq_neg_singularWindingClass (hU : ∀ x : X, ∃ i, x ∈ U i) :
    WindingCech.RationalCech.branchWindingClass X U hU b (WindingCech.RationalCech.branchCompatibility_of_global X U g hg b hb) =
      -WindingSingular.singularWindingClass X g hg := by
  let c := WindingCech.RationalCech.branchWindingCocycle X U b (WindingCech.RationalCech.branchCompatibility_of_global X U g hg b hb)
  let w := WindingSingular.singularWindingCocycle X g hg
  let T := Rational.CechComparison.RationalCech.singularCechTotal X U (ModuleCat.of ℚ ℚ)
  have hc : HomologicalComplex.homologyMap (Cech.Obj.RationalCech.locallyConstantCechToTotal X U) 1
      (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (Rational.Cech.RationalCech.cechComplex (Cech.Obj.RationalCech.locallyConstantPresheaf X) U) 1 c) =
    -HomologicalComplex.homologyMap (Rational.CechComparison.RationalCech.globalSingularCechAugmentation X U (ModuleCat.of ℚ ℚ)) 1
      (AlgebraicTopology.Cohomology.Singular.Representatives.singularClass (ModuleCat.of ℚ ℚ) X 1 w) := by
    rw [AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality, AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality, ← map_neg]
    apply (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_eq_iff_exists_succ T 0 _ _).mpr
    refine ⟨Rational.Cech.RationalCech.cechTotalInclusion U (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X) 0 0 0 rfl
      (branchPointPrimitives X U g hg b hb), ?_⟩
    change T.d 0 1 _ = (Cech.Obj.RationalCech.locallyConstantCechToTotal X U).f 1
        (WindingCech.RationalCech.branchWindingCech X U b (WindingCech.RationalCech.branchCompatibility_of_global X U g hg b hb)) -
      -((Rational.CechComparison.RationalCech.globalSingularCechAugmentation X U (ModuleCat.of ℚ ℚ)).f 1
        (WindingSingular.singularWindingCochain X g hg))
    rw [sub_neg_eq_add]
    exact branchPointPrimitives_total_d X U g hg b hb
  change (Rational.CechComparison.RationalCech.singularCechCohomologyIso X U hU 1).inv
      (HomologicalComplex.homologyMap (Cech.Obj.RationalCech.locallyConstantCechToTotal X U) 1
        (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (Rational.Cech.RationalCech.cechComplex (Cech.Obj.RationalCech.locallyConstantPresheaf X) U) 1 c)) = _
  rw [hc, map_neg]
  congr 1
  exact (Rational.CechComparison.RationalCech.singularCechCohomologyIso X U hU 1).hom_inv_id_apply
    (WindingSingular.singularWindingClass X g hg)

/-- The canonical logarithmic class has the now-proved singular path meaning. -/
theorem logarithmicWindingClass_eq_neg_singularWindingClass :
    WindingCech.RationalCech.logarithmicWindingClass X g hg = -WindingSingular.singularWindingClass X g hg :=
  branchWindingClass_eq_neg_singularWindingClass X (WindingCech.RationalCech.functionLogCover X g) g hg
    (WindingCech.RationalCech.functionLogBranches X g) (WindingCech.RationalCech.functionLogBranches_exp X g hg) (WindingCech.RationalCech.functionLogCover_covers X g hg)

end RationalCech

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.WindingComparisonD
