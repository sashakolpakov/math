import OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.Obj

/-! # Cech Transgression -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CechTransgression.Constructions

noncomputable section

/-!
# DegreeTwo: the degree-one Cech comparison from actual local primitives

The sign is computed from the actual total differential. If a family of local
zero-cochains has vertical coboundary `c` and horizontal coboundary `k`, then
the actual Cech-to-singular comparison sends `k` to `-c` in cohomology.
This is a statement about the existing comparison, not a chosen identification.
-/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.Obj.RationalCech

variable {I : Type} (X : TopCat.{0}) (U : I → Opens X)

/-- The degree-zero total coboundary is the sum of the horizontal and vertical
 coboundaries, with their actual inclusions into total degree one. -/
theorem cechZero_total_coboundary
    (t : DivisorClass.Chern.Rational.Cech.RationalCech.CechCochain (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf (ModuleCat.of ℚ ℚ) X 0) U 0) :
    (DivisorClass.Chern.Rational.CechComparison.RationalCech.singularCechTotal X U (ModuleCat.of ℚ ℚ)).d 0 1
      (DivisorClass.Chern.Rational.Cech.RationalCech.cechTotalInclusion U (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X) 0 0 0 rfl t) =
    DivisorClass.Chern.Rational.Cech.RationalCech.cechTotalInclusion U (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X) 1 0 1 rfl
      (DivisorClass.Chern.Rational.Cech.RationalCech.cechDelta (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf (ModuleCat.of ℚ ℚ) X 0) U 0 t) +
    DivisorClass.Chern.Rational.Cech.RationalCech.cechTotalInclusion U (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X) 0 1 1 rfl
      (DivisorClass.Chern.Rational.Cech.RationalCech.cechCoefficientMap U ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).d 0 1) 0 t) := by
  have h := ConcreteCategory.congr_hom
    (DivisorClass.Chern.Rational.Cech.RationalCech.cechTotalInclusion_d U (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X) 0 0 0 rfl) t
  change (DivisorClass.Chern.Rational.CechComparison.RationalCech.singularCechTotal X U (ModuleCat.of ℚ ℚ)).d 0 1
      (DivisorClass.Chern.Rational.Cech.RationalCech.cechTotalInclusion U (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X) 0 0 0 rfl t) =
    DivisorClass.Chern.Rational.Cech.RationalCech.cechTotalInclusion U (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X) 1 0 1 rfl
      (DivisorClass.Chern.Rational.Cech.RationalCech.cechDelta (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf (ModuleCat.of ℚ ℚ) X 0) U 0 t) +
    (-1 : ℤ) ^ 0 •
      DivisorClass.Chern.Rational.Cech.RationalCech.cechTotalInclusion U (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X) 0 1 1 rfl
        (DivisorClass.Chern.Rational.Cech.RationalCech.cechCoefficientMap U ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).d 0 1) 0 t) at h
  simpa only [pow_zero, one_zsmul] using h

/-- Local primitives identify the actual degree-one comparison, including its sign. -/
theorem cechClass_eq_neg_singularClass_of_primitives
    (hU : ∀ x : X, ∃ i, x ∈ U i)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X) 1)
    (k : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (DivisorClass.Chern.Rational.Cech.RationalCech.cechComplex (DivisorClass.Chern.Cech.Obj.RationalCech.locallyConstantPresheaf X) U) 1)
    (t : DivisorClass.Chern.Rational.Cech.RationalCech.CechCochain (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf (ModuleCat.of ℚ ℚ) X 0) U 0)
    (ht : DivisorClass.Chern.Rational.Cech.RationalCech.cechCoefficientMap U ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).d 0 1) 0 t =
      (DivisorClass.Chern.Rational.CechComparison.RationalCech.globalSingularCechColumnAugmentation X U (ModuleCat.of ℚ ℚ)).f 1 c.val)
    (hk : DivisorClass.Chern.Rational.Cech.RationalCech.cechDelta (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf (ModuleCat.of ℚ ℚ) X 0) U 0 t =
      DivisorClass.Chern.Cech.Obj.RationalCech.locallyConstantCechEvaluation X U 1 k.val) :
    DivisorClass.Chern.Cech.Obj.RationalCech.singularClassOfCechCocycle X U hU 1 k =
      -AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X) 1 c := by
  let T := DivisorClass.Chern.Rational.CechComparison.RationalCech.singularCechTotal X U (ModuleCat.of ℚ ℚ)
  let a := AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (DivisorClass.Chern.Cech.Obj.RationalCech.locallyConstantCechToTotal X U) 1 k
  let b := AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (DivisorClass.Chern.Rational.CechComparison.RationalCech.globalSingularCechAugmentation X U (ModuleCat.of ℚ ℚ)) 1 c
  have hab : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass T 1 a = AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass T 1 (-b) := by
    apply (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_eq_iff_exists_succ T 0 a (-b)).mpr
    refine ⟨DivisorClass.Chern.Rational.Cech.RationalCech.cechTotalInclusion U (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X) 0 0 0 rfl t, ?_⟩
    have hd := cechZero_total_coboundary X U t
    rw [ht, hk] at hd
    change T.d 0 1 _ = a.val - (-b).val
    change T.d 0 1 _ =
      (DivisorClass.Chern.Cech.Obj.RationalCech.locallyConstantCechToTotal X U).f 1 k.val -
        -((DivisorClass.Chern.Rational.CechComparison.RationalCech.globalSingularCechAugmentation X U (ModuleCat.of ℚ ℚ)).f 1 c.val)
    rw [sub_neg_eq_add, DivisorClass.Chern.Rational.CechComparison.RationalCech.globalSingularCechAugmentation_f]
    exact hd
  change AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass T 1 (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (DivisorClass.Chern.Cech.Obj.RationalCech.locallyConstantCechToTotal X U) 1 k) =
    AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass T 1 (-(AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap
      (DivisorClass.Chern.Rational.CechComparison.RationalCech.globalSingularCechAugmentation X U (ModuleCat.of ℚ ℚ)) 1 c)) at hab
  rw [map_neg, ← AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality, ← AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality] at hab
  apply (DivisorClass.Chern.Rational.CechComparison.RationalCech.singularCechCohomologyIso X U hU 1).toLinearEquiv.injective
  change (DivisorClass.Chern.Rational.CechComparison.RationalCech.singularCechCohomologyIso X U hU 1).hom
      ((DivisorClass.Chern.Rational.CechComparison.RationalCech.singularCechCohomologyIso X U hU 1).inv
        (HomologicalComplex.homologyMap (DivisorClass.Chern.Cech.Obj.RationalCech.locallyConstantCechToTotal X U) 1
          (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (DivisorClass.Chern.Rational.Cech.RationalCech.cechComplex (DivisorClass.Chern.Cech.Obj.RationalCech.locallyConstantPresheaf X) U) 1 k))) = _
  rw [Iso.inv_hom_id_apply, map_neg]
  exact hab

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CechTransgression.Constructions
