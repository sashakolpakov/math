/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Projective.LaurentCechData
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistCech

/-! # Twist Cech Weights -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistCechWeights.MvPolynomial

noncomputable section

open _root_.MvPolynomial

/-!
# Homogeneous-weight coordinates for the projective twist Cech complex

This file reindexes each standard-intersection factor of the existing ordered Cech complex by its
allowed global homogeneous Laurent weights.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace

universe u

variable {R : Type u} {σ : Type} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

local instance twistCechWeightsDecidableEq : DecidableEq σ := Classical.decEq σ

/-- The factorwise homogeneous-weight equivalences conjugate every geometric ordered Cech coface
to deletion of allowed global weights. -/
theorem coordinateHomogeneousLaurentOrderedCechCoface_naturality
    [LinearOrder σ] (d : ℤ) (n : ℕ) (k : Fin (n + 2)) :
    (LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechObjectIso
        (R := R) (σ := σ) d n).hom ≫
      LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechCoface
        (R := R) (σ := σ) d n k =
    TwistCech.MvPolynomial.coordinateHyperplaneTwistOrderedBaseCechCoface
        (R := R) (σ := σ) d n k ≫
      (LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechObjectIso
        (R := R) (σ := σ) d (n + 1)).hom := by
  unfold LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechObjectIso
  unfold LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechCoface
  apply Pi.hom_ext
  intro a
  erw [Category.assoc, Pi.lift_comp_π, Pi.mapIso_hom_π_assoc,
    Category.assoc, Pi.mapIso_hom_π]
  by_cases hk : k = 0
  · subst k
    rw [TwistCech.MvPolynomial.coordinateHyperplaneTwistOrderedBaseCechCoface, ite_eq_left rfl]
    conv_rhs =>
      erw [← Category.assoc,
        TwistCech.MvPolynomial.coordinateHyperplaneTwistOrderedBaseCechFirstCoface_comp_π]
    let p : OrderedBaseCech.Scheme.Modules.orderedBaseCechObject
        (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (Invertible.Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
        (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) n ⟶
      Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor
        (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (Invertible.Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
        (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) n (a.delete 0).1 :=
      Pi.π _ (a.delete 0)
    have hp :
        Pi.π (fun b : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
          Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor
            (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
            (Invertible.Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
            (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) n b.1) (a.delete 0) = p := rfl
    rw [hp]
    exact congrArg (fun f => p ≫ f)
      (LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentFactorCoface_naturality_delete_zero
        (R := R) a d)
  · obtain ⟨k, rfl⟩ := Fin.eq_succ_of_ne_zero hk
    rw [TwistCech.MvPolynomial.coordinateHyperplaneTwistOrderedBaseCechCoface,
      ite_eq_right (Fin.succ_ne_zero k)]
    conv_rhs =>
      erw [← Category.assoc, OrderedBaseCech.Scheme.Modules.orderedBaseCechCoface_comp_π]
    let p : OrderedBaseCech.Scheme.Modules.orderedBaseCechObject
        (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (Invertible.Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
        (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) n ⟶
      Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor
        (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (Invertible.Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
        (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) n (a.delete k.succ).1 :=
      Pi.π _ (a.delete k.succ)
    have hp :
        Pi.π (fun b : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
          Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor
            (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
            (Invertible.Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
            (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) n b.1)
          (a.delete k.succ) = p := rfl
    rw [hp]
    exact congrArg (fun f => p ≫ f)
      (LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentFactorCoface_naturality_delete_succ
        (R := R) a k d)

/-- The degreewise homogeneous-weight comparison conjugates the geometric coordinate differential
to the alternating deletion differential. -/
theorem coordinateHomogeneousLaurentOrderedCechDifferential_naturality
    [LinearOrder σ] (d : ℤ) (n : ℕ) :
    (LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechObjectIso
        (R := R) (σ := σ) d n).hom ≫
      LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechDifferential
        (R := R) (σ := σ) d n =
    TwistCech.MvPolynomial.coordinateHyperplaneTwistOrderedBaseCechDifferential
        (R := R) (σ := σ) d n ≫
      (LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechObjectIso
        (R := R) (σ := σ) d (n + 1)).hom := by
  rw [LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechDifferential,
    TwistCech.MvPolynomial.coordinateHyperplaneTwistOrderedBaseCechDifferential,
    Preadditive.comp_sum, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro k _
  rw [Preadditive.comp_zsmul, Preadditive.zsmul_comp,
    coordinateHomogeneousLaurentOrderedCechCoface_naturality]

/-- Consecutive homogeneous-weight differentials compose to zero. -/
theorem coordinateHomogeneousLaurentOrderedCechDifferential_comp
    [LinearOrder σ] (j : σ) (d : ℤ) (n : ℕ) :
    LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechDifferential
        (R := R) (σ := σ) d n ≫
      LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechDifferential
        (R := R) (σ := σ) d (n + 1) = 0 := by
  apply (cancel_epi
    (LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechObjectIso
      (R := R) (σ := σ) d n).hom).1
  rw [Limits.comp_zero, ← Category.assoc,
    coordinateHomogeneousLaurentOrderedCechDifferential_naturality,
    Category.assoc,
    coordinateHomogeneousLaurentOrderedCechDifferential_naturality,
    ← Category.assoc,
    TwistCech.MvPolynomial.coordinateHyperplaneTwistOrderedBaseCechDifferential_comp (R := R) j d n,
    Limits.zero_comp]

/-- The homogeneous-weight presentation of the ordered Cech complex for `O(d)`. -/
noncomputable def coordinateHomogeneousLaurentOrderedCechComplex
    [LinearOrder σ] (j : σ) (d : ℤ) :
    CochainComplex
      (ModuleCat.{u} Γ(Spec (CommRingCat.of R),
        (⊤ : (Spec (CommRingCat.of R)).Opens))) ℕ :=
  CochainComplex.of
    (LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechObject (R := R) (σ := σ) d)
    (LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechDifferential
      (R := R) (σ := σ) d)
    (coordinateHomogeneousLaurentOrderedCechDifferential_comp
      (R := R) j d)

@[simp]
theorem coordinateHomogeneousLaurentOrderedCechComplex_X
    [LinearOrder σ] (j : σ) (d : ℤ) (n : ℕ) :
    (coordinateHomogeneousLaurentOrderedCechComplex
      (R := R) j d).X n =
      LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechObject
        (R := R) (σ := σ) d n := rfl

@[simp]
theorem coordinateHomogeneousLaurentOrderedCechComplex_d
    [LinearOrder σ] (j : σ) (d : ℤ) (n : ℕ) :
    (coordinateHomogeneousLaurentOrderedCechComplex
      (R := R) j d).d n (n + 1) =
      LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechDifferential
        (R := R) (σ := σ) d n := by
  simp [coordinateHomogeneousLaurentOrderedCechComplex]

/-- The geometric coordinate Cech complex for `O(d)` is isomorphic to its homogeneous-weight
presentation. -/
noncomputable def coordinateHomogeneousLaurentOrderedCechComplexIso
    [LinearOrder σ] (j : σ) (d : ℤ) :
    TwistCech.MvPolynomial.coordinateHyperplaneTwistOrderedBaseCechComplex (R := R) j d ≅
      coordinateHomogeneousLaurentOrderedCechComplex (R := R) j d :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechObjectIso
      (R := R) (σ := σ) d n) (by
        intro n m hnm
        simp only [ComplexShape.up_Rel] at hnm
        subst m
        rw [TwistCech.MvPolynomial.coordinateHyperplaneTwistOrderedBaseCechComplex_d,
          coordinateHomogeneousLaurentOrderedCechComplex_d]
        exact coordinateHomogeneousLaurentOrderedCechDifferential_naturality
          (R := R) d n)

@[simp]
theorem coordinateHomogeneousLaurentOrderedCechComplexIso_hom_f
    [LinearOrder σ] (j : σ) (d : ℤ) (n : ℕ) :
    (coordinateHomogeneousLaurentOrderedCechComplexIso
      (R := R) j d).hom.f n =
      (LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechObjectIso
        (R := R) (σ := σ) d n).hom := rfl

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistCechWeights.MvPolynomial
