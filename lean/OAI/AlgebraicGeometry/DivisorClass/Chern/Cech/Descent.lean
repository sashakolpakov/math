import OAI.AlgebraicGeometry.DivisorClass.Chern.Singular.CechDescent
import OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexDifferential

/-! # Descent -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.DivisorClass.Chern
open _root_.CategoryTheory
open _root_.TopologicalSpace
section

/-! Locally constant rational two-cocycles obtained from actual singular descent. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}} {I : Type} (U : I → Opens X)

theorem Cech.Descent.locallyConstantCechEvaluation_injective (n : ℕ) :
    Function.Injective (Cech.Obj.RationalCech.locallyConstantCechEvaluation X U n) := by
  intro f g h
  funext a
  exact AlgebraicTopology.Cohomology.Singular.Augmentation.locallyConstantToSingularZero_injective (ModuleCat.of ℚ ℚ)
    (TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)) (congrFun h a)

theorem Cech.Descent.exists_locallyConstantCechEvaluation [LocallyPathConnectedSpace X] (n : ℕ)
    (k : Rational.Cech.RationalCech.CechCochain ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).X 0) U n)
    (hk : Rational.Cech.RationalCech.cechCoefficientMap U ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).d 0 1) n k = 0) :
    ∃ f : Rational.Cech.RationalCech.CechCochain (Cech.Obj.RationalCech.locallyConstantPresheaf X) U n,
      Cech.Obj.RationalCech.locallyConstantCechEvaluation X U n f = k := by
  have h (a : Fin (n + 1) → I) :
      ∃ f : LocallyConstant (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) ℚ,
        AlgebraicTopology.Cohomology.Singular.Augmentation.locallyConstantToSingularZero (ModuleCat.of ℚ ℚ)
          (TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)) f = k a := by
    have : LocallyPathConnectedSpace (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) :=
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a).isOpen.locallyPathConnectedSpace
    change k a ∈ LinearMap.range (AlgebraicTopology.Cohomology.Singular.Augmentation.locallyConstantToSingularZero (ModuleCat.of ℚ ℚ)
      (TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a))).hom
    rw [AlgebraicTopology.Cohomology.Singular.Augmentation.locallyConstantToSingularZero_range_eq_ker]
    exact congrFun hk a
  choose f hf using h
  exact ⟨f, funext hf⟩

variable {U} {c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of ℚ ℚ) X 2} (d : Singular.CechDescent.SingularCechDescentData c U)

theorem Singular.CechDescent.SingularCechDescentData.horizontal_delta_closed :
    Rational.Cech.RationalCech.cechCoefficientMap U ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).d 0 1) 2
      (-Rational.Cech.RationalCech.cechDelta ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).X 0) U 1 d.horizontal) = 0 := by
  rw [map_neg, Rational.Cech.RationalCech.cechCoefficientMap_delta, d.horizontal_d, Rational.Cech.RationalCech.cechDelta_squared, neg_zero]

theorem Singular.CechDescent.SingularCechDescentData.exists_cechCocycle [LocallyPathConnectedSpace X] :
    ∃ k : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (Rational.Cech.RationalCech.cechComplex (Cech.Obj.RationalCech.locallyConstantPresheaf X) U) 2,
      Cech.Obj.RationalCech.locallyConstantCechEvaluation X U 2 k.val =
        -Rational.Cech.RationalCech.cechDelta ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).X 0) U 1 d.horizontal := by
  obtain ⟨k, hk⟩ := Cech.Descent.exists_locallyConstantCechEvaluation U 2 _ d.horizontal_delta_closed
  have hclosed : Rational.Cech.RationalCech.cechDelta (Cech.Obj.RationalCech.locallyConstantPresheaf X) U 2 k = 0 := by
    apply Cech.Descent.locallyConstantCechEvaluation_injective U 3
    rw [Rational.Cech.RationalCech.cechCoefficientMap_delta, hk, map_neg]
    erw [Rational.Cech.RationalCech.cechDelta_squared, neg_zero, map_zero]
  exact ⟨⟨k, by erw [AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff, Rational.Cech.RationalCech.cechComplex_d]; exact hclosed⟩, hk⟩

end

/-! The descended Cech cocycle represents the original singular class. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}} {I : Type} {U : I → Opens X}
  {c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of ℚ ℚ) X 2} (d : Singular.CechDescent.SingularCechDescentData c U)

def Singular.CechDescent.SingularCechDescentData.totalPrimitive : (Rational.CechComparison.RationalCech.singularCechTotal X U (ModuleCat.of ℚ ℚ)).X 1 :=
  -Rational.Cech.RationalCech.cechTotalInclusion U (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X) 1 0 1 rfl d.horizontal -
    Rational.Cech.RationalCech.cechTotalInclusion U (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X) 0 1 1 rfl d.vertical

theorem Singular.CechDescent.SingularCechDescentData.totalPrimitive_d
    (k : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (Rational.Cech.RationalCech.cechComplex (Cech.Obj.RationalCech.locallyConstantPresheaf X) U) 2)
    (hk : Cech.Obj.RationalCech.locallyConstantCechEvaluation X U 2 k.val =
      -Rational.Cech.RationalCech.cechDelta ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).X 0) U 1 d.horizontal) :
    (Rational.CechComparison.RationalCech.singularCechTotal X U (ModuleCat.of ℚ ℚ)).d 1 2 d.totalPrimitive =
      (Cech.Obj.RationalCech.locallyConstantCechToTotal X U).f 2 k.val -
        (Rational.CechComparison.RationalCech.globalSingularCechAugmentation X U (ModuleCat.of ℚ ℚ)).f 2 c.val := by
  let C := AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X
  have hh := ConcreteCategory.congr_hom (Rational.Cech.RationalCech.cechTotalInclusion_d U C 1 0 1 rfl) d.horizontal
  have hv := ConcreteCategory.congr_hom (Rational.Cech.RationalCech.cechTotalInclusion_d U C 0 1 1 rfl) d.vertical
  change (Rational.CechComparison.RationalCech.singularCechTotal X U (ModuleCat.of ℚ ℚ)).d 1 2
      (Rational.Cech.RationalCech.cechTotalInclusion U C 1 0 1 rfl d.horizontal) =
    Rational.Cech.RationalCech.cechTotalInclusion U C 2 0 2 rfl (Rational.Cech.RationalCech.cechDelta (C.X 0) U 1 d.horizontal) +
      (-1 : ℤ) • Rational.Cech.RationalCech.cechTotalInclusion U C 1 1 2 rfl
        (Rational.Cech.RationalCech.cechCoefficientMap U (C.d 0 1) 1 d.horizontal) at hh
  change (Rational.CechComparison.RationalCech.singularCechTotal X U (ModuleCat.of ℚ ℚ)).d 1 2
      (Rational.Cech.RationalCech.cechTotalInclusion U C 0 1 1 rfl d.vertical) =
    Rational.Cech.RationalCech.cechTotalInclusion U C 1 1 2 rfl (Rational.Cech.RationalCech.cechDelta (C.X 1) U 0 d.vertical) +
      (1 : ℤ) • Rational.Cech.RationalCech.cechTotalInclusion U C 0 2 2 rfl
        (Rational.Cech.RationalCech.cechCoefficientMap U (C.d 1 2) 0 d.vertical) at hv
  rw [neg_one_zsmul, d.horizontal_d] at hh
  rw [one_zsmul, d.vertical_d] at hv
  change (Rational.CechComparison.RationalCech.singularCechTotal X U (ModuleCat.of ℚ ℚ)).d 1 2
      (-Rational.Cech.RationalCech.cechTotalInclusion U C 1 0 1 rfl d.horizontal -
        Rational.Cech.RationalCech.cechTotalInclusion U C 0 1 1 rfl d.vertical) =
    Rational.Cech.RationalCech.cechTotalInclusion U C 2 0 2 rfl (Cech.Obj.RationalCech.locallyConstantCechEvaluation X U 2 k.val) -
      Rational.Cech.RationalCech.cechTotalInclusion U C 0 2 2 rfl
        ((Rational.CechComparison.RationalCech.globalSingularCechColumnAugmentation X U (ModuleCat.of ℚ ℚ)).f 2 c.val)
  rw [map_sub, map_neg, hh, hv, hk, map_neg]
  exact (show ∀ x y z : (Rational.CechComparison.RationalCech.singularCechTotal X U (ModuleCat.of ℚ ℚ)).X 2,
    -(x + -y) - (y + z) = -x - z from by intros; abel) _ _ _

theorem Singular.CechDescent.SingularCechDescentData.singularClass_eq
    (hU : ∀ x : X, ∃ i, x ∈ U i)
    (k : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (Rational.Cech.RationalCech.cechComplex (Cech.Obj.RationalCech.locallyConstantPresheaf X) U) 2)
    (hk : Cech.Obj.RationalCech.locallyConstantCechEvaluation X U 2 k.val =
      -Rational.Cech.RationalCech.cechDelta ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).X 0) U 1 d.horizontal) :
    Cech.Obj.RationalCech.singularClassOfCechCocycle X U hU 2 k = AlgebraicTopology.Cohomology.Singular.Representatives.singularClass (ModuleCat.of ℚ ℚ) X 2 c := by
  have he : HomologicalComplex.homologyMap (Cech.Obj.RationalCech.locallyConstantCechToTotal X U) 2
      (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (Rational.Cech.RationalCech.cechComplex (Cech.Obj.RationalCech.locallyConstantPresheaf X) U) 2 k) =
    HomologicalComplex.homologyMap (Rational.CechComparison.RationalCech.globalSingularCechAugmentation X U (ModuleCat.of ℚ ℚ)) 2
      (AlgebraicTopology.Cohomology.Singular.Representatives.singularClass (ModuleCat.of ℚ ℚ) X 2 c) := by
    rw [AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality, AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality]
    apply (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_eq_iff_exists_succ (Rational.CechComparison.RationalCech.singularCechTotal X U (ModuleCat.of ℚ ℚ)) 1 _ _).mpr
    exact ⟨d.totalPrimitive, d.totalPrimitive_d k hk⟩
  change (Rational.CechComparison.RationalCech.singularCechCohomologyIso X U hU 2).inv
      (HomologicalComplex.homologyMap (Cech.Obj.RationalCech.locallyConstantCechToTotal X U) 2
        (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (Rational.Cech.RationalCech.cechComplex (Cech.Obj.RationalCech.locallyConstantPresheaf X) U) 2 k)) = _
  rw [he]
  exact (Rational.CechComparison.RationalCech.singularCechCohomologyIso X U hU 2).hom_inv_id_apply _

theorem Cech.Descent.exists_rationalCechTwoRepresentative [CompactSpace X] [NormalSpace X]
    [StronglyLocallyContractibleSpace X] [LocallyPathConnectedSpace X]
    (a : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X 2) :
    ∃ (I : Type) (U : I → Opens X) (hU : ∀ x, ∃ i, x ∈ U i)
      (k : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (Rational.Cech.RationalCech.cechComplex (Cech.Obj.RationalCech.locallyConstantPresheaf X) U) 2),
      Cech.Obj.RationalCech.singularClassOfCechCocycle X U hU 2 k = a := by
  obtain ⟨c, rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.singularClass_surjective (ModuleCat.of ℚ ℚ) X 2 a
  obtain ⟨I, U, hU, ⟨d⟩⟩ := Singular.CechDescent.exists_singularCechDescentData c
  obtain ⟨k, hk⟩ := d.exists_cechCocycle
  exact ⟨I, U, hU, k, d.singularClass_eq hU k hk⟩

end AlgebraicGeometry.DivisorClass.Chern

namespace AlgebraicGeometry.DivisorClass.Chern.Cech.Descent

/-! Recover actual singular descent from a boundary between the two Cech edges. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexDifferential.DoubleComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}} {I : Type} (U : I → Opens X)

theorem singularCech_project_inclusion_self (p q n : ℕ) (hpq : p + q = n)
    (x : Rational.Cech.RationalCech.CechCochain ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).X q) U p) :
    AlgebraicTopology.DeRham.Comparison.DoubleComplexProjections.DoubleComplex.πTotal (Rational.Cech.RationalCech.cechDoubleComplex U (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X)) p q n hpq
      (Rational.Cech.RationalCech.cechTotalInclusion U (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X) p q n hpq x) = x :=
  ConcreteCategory.congr_hom (AlgebraicTopology.DeRham.Comparison.DoubleComplexProjections.DoubleComplex.iota_πTotal_self
    (Rational.Cech.RationalCech.cechDoubleComplex U (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X)) p q n hpq) x

theorem singularCech_project_inclusion_ne (p q a b n : ℕ)
    (hpq : p + q = n) (hab : a + b = n) (hne : (p, q) ≠ (a, b))
    (x : Rational.Cech.RationalCech.CechCochain ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).X q) U p) :
    AlgebraicTopology.DeRham.Comparison.DoubleComplexProjections.DoubleComplex.πTotal (Rational.Cech.RationalCech.cechDoubleComplex U (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X)) a b n hab
      (Rational.Cech.RationalCech.cechTotalInclusion U (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X) p q n hpq x) = 0 :=
  ConcreteCategory.congr_hom (AlgebraicTopology.DeRham.Comparison.DoubleComplexProjections.DoubleComplex.iota_πTotal_ne
    (Rational.Cech.RationalCech.cechDoubleComplex U (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X)) p q a b n hpq hab hne) x

variable {U} (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of ℚ ℚ) X 2)
  (k : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (Rational.Cech.RationalCech.cechComplex (Obj.RationalCech.locallyConstantPresheaf X) U) 2)
  (b : (Rational.CechComparison.RationalCech.singularCechTotal X U (ModuleCat.of ℚ ℚ)).X 1)
  (hb : (Rational.CechComparison.RationalCech.singularCechTotal X U (ModuleCat.of ℚ ℚ)).d 1 2 b =
    (Obj.RationalCech.locallyConstantCechToTotal X U).f 2 k.val -
      (Rational.CechComparison.RationalCech.globalSingularCechAugmentation X U (ModuleCat.of ℚ ℚ)).f 2 c.val)

include hb in
theorem singularCechBoundary_vertical :
    Rational.Cech.RationalCech.cechCoefficientMap U ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).d 1 2) 0
      (-AlgebraicTopology.DeRham.Comparison.DoubleComplexProjections.DoubleComplex.πTotal (Rational.Cech.RationalCech.cechDoubleComplex U (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X)) 0 1 1 rfl b) =
        (Rational.CechComparison.RationalCech.globalSingularCechColumnAugmentation X U (ModuleCat.of ℚ ℚ)).f 2 c.val := by
  let K := Rational.Cech.RationalCech.cechDoubleComplex U (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X)
  have h := congrArg (AlgebraicTopology.DeRham.Comparison.DoubleComplexProjections.DoubleComplex.πTotal K 0 2 2 rfl) hb
  rw [AlgebraicTopology.DeRham.Comparison.DoubleComplexDifferential.DoubleComplex.project_d_zero_succ K 1 1 rfl] at h
  change Rational.Cech.RationalCech.cechCoefficientMap U ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).d 1 2) 0
    (AlgebraicTopology.DeRham.Comparison.DoubleComplexProjections.DoubleComplex.πTotal K 0 1 1 rfl b) = AlgebraicTopology.DeRham.Comparison.DoubleComplexProjections.DoubleComplex.πTotal K 0 2 2 rfl
      (Rational.Cech.RationalCech.cechTotalInclusion U (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X) 2 0 2 rfl
        (Obj.RationalCech.locallyConstantCechEvaluation X U 2 k.val) -
       Rational.Cech.RationalCech.cechTotalInclusion U (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X) 0 2 2 rfl
        ((Rational.CechComparison.RationalCech.globalSingularCechColumnAugmentation X U (ModuleCat.of ℚ ℚ)).f 2 c.val)) at h
  rw [map_sub] at h
  erw [singularCech_project_inclusion_ne U 2 0 0 2 2 rfl rfl (by decide),
    singularCech_project_inclusion_self, zero_sub] at h
  rw [map_neg, h, neg_neg]

include hb in
theorem singularCechBoundary_middle :
    Rational.Cech.RationalCech.cechCoefficientMap U ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).d 0 1) 1
      (-AlgebraicTopology.DeRham.Comparison.DoubleComplexProjections.DoubleComplex.πTotal (Rational.Cech.RationalCech.cechDoubleComplex U (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X)) 1 0 1 rfl b) =
        Rational.Cech.RationalCech.cechDelta ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).X 1) U 0
          (-AlgebraicTopology.DeRham.Comparison.DoubleComplexProjections.DoubleComplex.πTotal (Rational.Cech.RationalCech.cechDoubleComplex U (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X)) 0 1 1 rfl b) := by
  let K := Rational.Cech.RationalCech.cechDoubleComplex U (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X)
  have h := congrArg (AlgebraicTopology.DeRham.Comparison.DoubleComplexProjections.DoubleComplex.πTotal K 1 1 2 rfl) hb
  rw [AlgebraicTopology.DeRham.Comparison.DoubleComplexDifferential.DoubleComplex.project_d_succ_succ K 0 0 1 rfl] at h
  change Rational.Cech.RationalCech.cechDelta ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).X 1) U 0
      (AlgebraicTopology.DeRham.Comparison.DoubleComplexProjections.DoubleComplex.πTotal K 0 1 1 rfl b) + (-1 : ℤ) ^ 1 •
        Rational.Cech.RationalCech.cechCoefficientMap U ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).d 0 1) 1
          (AlgebraicTopology.DeRham.Comparison.DoubleComplexProjections.DoubleComplex.πTotal K 1 0 1 rfl b) = AlgebraicTopology.DeRham.Comparison.DoubleComplexProjections.DoubleComplex.πTotal K 1 1 2 rfl
      (Rational.Cech.RationalCech.cechTotalInclusion U (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X) 2 0 2 rfl
        (Obj.RationalCech.locallyConstantCechEvaluation X U 2 k.val) -
       Rational.Cech.RationalCech.cechTotalInclusion U (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X) 0 2 2 rfl
        ((Rational.CechComparison.RationalCech.globalSingularCechColumnAugmentation X U (ModuleCat.of ℚ ℚ)).f 2 c.val)) at h
  rw [map_sub] at h
  erw [singularCech_project_inclusion_ne U 2 0 1 1 2 rfl rfl (by decide),
    singularCech_project_inclusion_ne U 0 2 1 1 2 rfl rfl (by decide),
    sub_self, pow_one, neg_one_zsmul, ← sub_eq_add_neg, sub_eq_zero] at h
  rw [map_neg, map_neg, h]

include hb in
theorem singularCechBoundary_horizontal :
    Obj.RationalCech.locallyConstantCechEvaluation X U 2 k.val =
      -Rational.Cech.RationalCech.cechDelta ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).X 0) U 1
        (-AlgebraicTopology.DeRham.Comparison.DoubleComplexProjections.DoubleComplex.πTotal (Rational.Cech.RationalCech.cechDoubleComplex U (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X)) 1 0 1 rfl b) := by
  let K := Rational.Cech.RationalCech.cechDoubleComplex U (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X)
  have h := congrArg (AlgebraicTopology.DeRham.Comparison.DoubleComplexProjections.DoubleComplex.πTotal K 2 0 2 rfl) hb
  rw [AlgebraicTopology.DeRham.Comparison.DoubleComplexDifferential.DoubleComplex.project_d_succ_zero K 1 1 rfl] at h
  change Rational.Cech.RationalCech.cechDelta ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).X 0) U 1
    (AlgebraicTopology.DeRham.Comparison.DoubleComplexProjections.DoubleComplex.πTotal K 1 0 1 rfl b) = AlgebraicTopology.DeRham.Comparison.DoubleComplexProjections.DoubleComplex.πTotal K 2 0 2 rfl
      (Rational.Cech.RationalCech.cechTotalInclusion U (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X) 2 0 2 rfl
        (Obj.RationalCech.locallyConstantCechEvaluation X U 2 k.val) -
       Rational.Cech.RationalCech.cechTotalInclusion U (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X) 0 2 2 rfl
        ((Rational.CechComparison.RationalCech.globalSingularCechColumnAugmentation X U (ModuleCat.of ℚ ℚ)).f 2 c.val)) at h
  rw [map_sub] at h
  erw [singularCech_project_inclusion_self,
    singularCech_project_inclusion_ne U 0 2 2 0 2 rfl rfl (by decide), sub_zero] at h
  rw [map_neg, neg_neg]
  exact h.symm

def singularCechDescentOfBoundary : Singular.CechDescent.SingularCechDescentData c U where
  vertical := -AlgebraicTopology.DeRham.Comparison.DoubleComplexProjections.DoubleComplex.πTotal (Rational.Cech.RationalCech.cechDoubleComplex U (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X)) 0 1 1 rfl b
  vertical_d := singularCechBoundary_vertical c k b hb
  horizontal := -AlgebraicTopology.DeRham.Comparison.DoubleComplexProjections.DoubleComplex.πTotal (Rational.Cech.RationalCech.cechDoubleComplex U (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X)) 1 0 1 rfl b
  horizontal_d := singularCechBoundary_middle c k b hb

theorem singularCechDescentOfBoundary_cocycle :
    Obj.RationalCech.locallyConstantCechEvaluation X U 2 k.val =
      -Rational.Cech.RationalCech.cechDelta ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).X 0) U 1
        (singularCechDescentOfBoundary c k b hb).horizontal :=
  singularCechBoundary_horizontal c k b hb

end AlgebraicGeometry.DivisorClass.Chern.Cech.Descent

end

end OAI
