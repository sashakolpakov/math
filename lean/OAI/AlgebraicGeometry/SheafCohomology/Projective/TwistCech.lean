/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistCechFirstFrame
import OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseFrameNaturality
import OAI.AlgebraicGeometry.SheafCohomology.Projective.IntegerTwistTransitions

/-! # Twist Cech -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistCech.MvPolynomial

noncomputable section

open _root_.MvPolynomial

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace
universe u
variable {R : Type u} {σ : Type} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The first Cech face is ordinary restriction followed by multiplication
by the restricted integer-twist transition unit. -/
theorem coordinateHyperplaneTwistBaseCechFactorIsoUnit_naturality_delete_zero
    [LinearOrder σ] {n : ℕ}
    (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (j : σ) (d : ℤ) :
    (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf
        (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j d)).map
          (StandardCech.MvPolynomial.coordinateOpenCechDelete (R := R) a 0).op ≫
      (TwistCechFactors.MvPolynomial.coordinateHyperplaneTwistBaseCechFactorIsoUnit
        (R := R) a.1 j d).hom =
    (TwistCechFactors.MvPolynomial.coordinateHyperplaneTwistBaseCechFactorIsoUnit
        (R := R) (a.delete 0).1 j d).hom ≫
      (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf
        (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (Invertible.Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))).map
          (StandardCech.MvPolynomial.coordinateOpenCechDelete (R := R) a 0).op ≫
      TwistCechFactors.MvPolynomial.coordinateOpenCechFirstTransitionFactorEnd (R := R) a d := by
  apply BaseFrameNaturality.MvPolynomial.baseModulePresheafFrame_naturality_scalar
  change _ = _ ≫ UnitScalar.unitEndomorphismOfTopSection _
  rw [← TwistCechFactors.MvPolynomial.coordinateOpenCechFirstTransitionTopUnit_zpow_coe]
  exact TwistCechFirstFrame.MvPolynomial.coordinateHyperplaneTwistCechTrivialization_restrict_delete_zero (R := R) a j d

/-- The degree-`n` ordered Cech object of `O(d)` is factorwise identified with
the ordered Cech object of the structure sheaf. -/
noncomputable def coordinateHyperplaneTwistOrderedBaseCechObjectIsoUnit
    [LinearOrder σ] (j : σ) (d : ℤ) (n : ℕ) :
    OrderedBaseCech.Scheme.Modules.orderedBaseCechObject
        (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j d)
        (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) n ≅
      OrderedBaseCech.Scheme.Modules.orderedBaseCechObject
        (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (Invertible.Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
        (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) n :=
  Pi.mapIso (fun a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
    TwistCechFactors.MvPolynomial.coordinateHyperplaneTwistBaseCechFactorIsoUnit (R := R) a.1 j d)

/-- The degreewise twist-to-unit Cech comparison is the landed factor
comparison on every ordered tuple. -/
@[reassoc]
theorem coordinateHyperplaneTwistOrderedBaseCechObjectIsoUnit_hom_comp_π
    [LinearOrder σ] (j : σ) (d : ℤ) (n : ℕ)
    (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n) :
    (coordinateHyperplaneTwistOrderedBaseCechObjectIsoUnit
        (R := R) j d n).hom ≫
      Pi.π (fun b : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
        Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor
          (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
          (Invertible.Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
          (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) n b.1) a =
    Pi.π (fun b : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
      Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor
        (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j d)
        (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) n b.1) a ≫
      (TwistCechFactors.MvPolynomial.coordinateHyperplaneTwistBaseCechFactorIsoUnit
        (R := R) a.1 j d).hom := by
  exact Pi.mapIso_hom_π
    (fun b : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
      TwistCechFactors.MvPolynomial.coordinateHyperplaneTwistBaseCechFactorIsoUnit (R := R) b.1 j d) a

/-- Every noninitial ordered Cech coface becomes ordinary structure-sheaf
restriction in the standard twist frames. -/
theorem coordinateHyperplaneTwistOrderedBaseCechCoface_of_ne_zero
    [LinearOrder σ] (j : σ) (d : ℤ) (n : ℕ)
    (k : Fin (n + 2)) (hk : k ≠ 0) :
    (coordinateHyperplaneTwistOrderedBaseCechObjectIsoUnit
        (R := R) j d n).hom ≫
      OrderedBaseCech.Scheme.Modules.orderedBaseCechCoface
        (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (Invertible.Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
        (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) n k =
    OrderedBaseCech.Scheme.Modules.orderedBaseCechCoface
        (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j d)
        (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) n k ≫
      (coordinateHyperplaneTwistOrderedBaseCechObjectIsoUnit
        (R := R) j d (n + 1)).hom := by
  unfold coordinateHyperplaneTwistOrderedBaseCechObjectIsoUnit
  unfold OrderedBaseCech.Scheme.Modules.orderedBaseCechCoface
  unfold OrderedBaseCech.Scheme.Modules.orderedBaseCechObject
  unfold FormalCoproduct.evalOp
  apply Pi.hom_ext
  intro a
  erw [Category.assoc, Pi.lift_comp_π, Pi.mapIso_hom_π_assoc,
    Category.assoc, Pi.mapIso_hom_π]
  conv_rhs => erw [← Category.assoc, Pi.lift_comp_π]
  let a' : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1) := a
  change Pi.π (fun b : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
      Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor
        (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j d)
        (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) n b.1) (a'.delete k) ≫
      ((TwistCechFactors.MvPolynomial.coordinateHyperplaneTwistBaseCechFactorIsoUnit
          (R := R) (a'.delete k).1 j d).hom ≫
        (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf
          (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
          (Invertible.Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))).map
            (StandardCech.MvPolynomial.coordinateOpenCechDelete (R := R) a' k).op) =
    Pi.π (fun b : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
      Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor
        (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j d)
        (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) n b.1) (a'.delete k) ≫
      ((Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf
          (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
          (TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j d)).map
            (StandardCech.MvPolynomial.coordinateOpenCechDelete (R := R) a' k).op ≫
        (TwistCechFactors.MvPolynomial.coordinateHyperplaneTwistBaseCechFactorIsoUnit
          (R := R) a'.1 j d).hom)
  have hNat :=
    TwistCechFirstFrame.MvPolynomial.coordinateHyperplaneTwistBaseCechFactorIsoUnit_naturality_delete_of_ne_zero
    (R := R) a' k hk j d
  exact congrArg
    (fun q =>
      Pi.π (fun b : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
        Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor
          (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
          (TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j d)
          (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) n b.1) (a'.delete k) ≫ q)
    hNat.symm

/-- The first coface in standard twist coordinates: ordinary restriction
followed by multiplication by the first-chart transition factor. -/
noncomputable def coordinateHyperplaneTwistOrderedBaseCechFirstCoface
    [LinearOrder σ] (d : ℤ) (n : ℕ) :
    OrderedBaseCech.Scheme.Modules.orderedBaseCechObject
        (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (Invertible.Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
        (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) n ⟶
      OrderedBaseCech.Scheme.Modules.orderedBaseCechObject
        (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (Invertible.Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
        (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) (n + 1) :=
  Pi.lift fun a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1) =>
    Pi.π (fun b : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
      Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor
        (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (Invertible.Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
        (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) n b.1) (a.delete 0) ≫
      (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf
        (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (Invertible.Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))).map
          (StandardCech.MvPolynomial.coordinateOpenCechDelete (R := R) a 0).op ≫
      TwistCechFactors.MvPolynomial.coordinateOpenCechFirstTransitionFactorEnd (R := R) a d

/-- The first coordinate coface has the advertised restriction-and-transition
formula on every ordered tuple. -/
@[reassoc]
theorem coordinateHyperplaneTwistOrderedBaseCechFirstCoface_comp_π
    [LinearOrder σ] (d : ℤ) (n : ℕ)
    (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) :
    coordinateHyperplaneTwistOrderedBaseCechFirstCoface
        (R := R) d n ≫
      Pi.π (fun b : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1) =>
        Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor
          (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
          (Invertible.Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
          (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) (n + 1) b.1) a =
    Pi.π (fun b : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
      Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor
        (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (Invertible.Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
        (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) n b.1) (a.delete 0) ≫
      (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf
        (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (Invertible.Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))).map
          (StandardCech.MvPolynomial.coordinateOpenCechDelete (R := R) a 0).op ≫
      TwistCechFactors.MvPolynomial.coordinateOpenCechFirstTransitionFactorEnd (R := R) a d := by
  exact Pi.lift_comp_π _ a

/-- The exceptional first twist coface becomes the coordinate coface carrying
the first-chart transition factor. -/
theorem coordinateHyperplaneTwistOrderedBaseCechCoface_zero
    [LinearOrder σ] (j : σ) (d : ℤ) (n : ℕ) :
    (coordinateHyperplaneTwistOrderedBaseCechObjectIsoUnit
        (R := R) j d n).hom ≫
      coordinateHyperplaneTwistOrderedBaseCechFirstCoface
        (R := R) d n =
    OrderedBaseCech.Scheme.Modules.orderedBaseCechCoface
        (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j d)
        (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) n 0 ≫
      (coordinateHyperplaneTwistOrderedBaseCechObjectIsoUnit
        (R := R) j d (n + 1)).hom := by
  unfold coordinateHyperplaneTwistOrderedBaseCechFirstCoface
  unfold coordinateHyperplaneTwistOrderedBaseCechObjectIsoUnit
  unfold OrderedBaseCech.Scheme.Modules.orderedBaseCechCoface
  unfold OrderedBaseCech.Scheme.Modules.orderedBaseCechObject
  unfold FormalCoproduct.evalOp
  apply Pi.hom_ext
  intro a
  erw [Category.assoc, Pi.lift_comp_π, Pi.mapIso_hom_π_assoc,
    Category.assoc, Pi.mapIso_hom_π]
  conv_rhs => erw [← Category.assoc, Pi.lift_comp_π]
  let a' : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1) := a
  change Pi.π (fun b : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
      Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor
        (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j d)
        (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) n b.1) (a'.delete 0) ≫
      ((TwistCechFactors.MvPolynomial.coordinateHyperplaneTwistBaseCechFactorIsoUnit
          (R := R) (a'.delete 0).1 j d).hom ≫
        (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf
          (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
          (Invertible.Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))).map
            (StandardCech.MvPolynomial.coordinateOpenCechDelete (R := R) a' 0).op ≫
        TwistCechFactors.MvPolynomial.coordinateOpenCechFirstTransitionFactorEnd (R := R) a' d) =
    Pi.π (fun b : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
      Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor
        (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j d)
        (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) n b.1) (a'.delete 0) ≫
      ((Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf
          (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
          (TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j d)).map
            (StandardCech.MvPolynomial.coordinateOpenCechDelete (R := R) a' 0).op ≫
        (TwistCechFactors.MvPolynomial.coordinateHyperplaneTwistBaseCechFactorIsoUnit
          (R := R) a'.1 j d).hom)
  have hNat :=
    coordinateHyperplaneTwistBaseCechFactorIsoUnit_naturality_delete_zero
      (R := R) a' j d
  exact congrArg
    (fun q =>
      Pi.π (fun b : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
        Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor
          (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
          (TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j d)
          (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) n b.1) (a'.delete 0) ≫ q)
    hNat.symm

/-- The ordered Cech coface in standard twist coordinates. Only the first
face carries a transition factor. -/
noncomputable def coordinateHyperplaneTwistOrderedBaseCechCoface
    [LinearOrder σ] (d : ℤ) (n : ℕ) (k : Fin (n + 2)) :
    OrderedBaseCech.Scheme.Modules.orderedBaseCechObject
        (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (Invertible.Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
        (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) n ⟶
      OrderedBaseCech.Scheme.Modules.orderedBaseCechObject
        (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (Invertible.Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
        (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) (n + 1) :=
  if k = 0 then
    coordinateHyperplaneTwistOrderedBaseCechFirstCoface (R := R) d n
  else
    OrderedBaseCech.Scheme.Modules.orderedBaseCechCoface
      (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      (Invertible.Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
      (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) n k

/-- The degreewise twist comparison intertwines every twist coface with its
explicit coordinate coface. -/
theorem coordinateHyperplaneTwistOrderedBaseCechCoface_naturality
    [LinearOrder σ] (j : σ) (d : ℤ) (n : ℕ) (k : Fin (n + 2)) :
    (coordinateHyperplaneTwistOrderedBaseCechObjectIsoUnit
        (R := R) j d n).hom ≫
      coordinateHyperplaneTwistOrderedBaseCechCoface
        (R := R) d n k =
    OrderedBaseCech.Scheme.Modules.orderedBaseCechCoface
        (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j d)
        (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) n k ≫
      (coordinateHyperplaneTwistOrderedBaseCechObjectIsoUnit
        (R := R) j d (n + 1)).hom := by
  by_cases hk : k = 0
  · subst k
    exact coordinateHyperplaneTwistOrderedBaseCechCoface_zero
      (R := R) j d n
  · rw [coordinateHyperplaneTwistOrderedBaseCechCoface, ite_eq_right hk]
    exact coordinateHyperplaneTwistOrderedBaseCechCoface_of_ne_zero
      (R := R) j d n k hk

/-- The alternating ordered Cech differential in standard twist coordinates. -/
noncomputable def coordinateHyperplaneTwistOrderedBaseCechDifferential
    [LinearOrder σ] (d : ℤ) (n : ℕ) :
    OrderedBaseCech.Scheme.Modules.orderedBaseCechObject
        (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (Invertible.Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
        (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) n ⟶
      OrderedBaseCech.Scheme.Modules.orderedBaseCechObject
        (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (Invertible.Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
        (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) (n + 1) :=
  ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
    coordinateHyperplaneTwistOrderedBaseCechCoface (R := R) d n k

/-- The degreewise standard-frame comparison conjugates the twist Cech
differential to the explicit coordinate differential. -/
theorem coordinateHyperplaneTwistOrderedBaseCechDifferential_naturality
    [LinearOrder σ] (j : σ) (d : ℤ) (n : ℕ) :
    (coordinateHyperplaneTwistOrderedBaseCechObjectIsoUnit
        (R := R) j d n).hom ≫
      coordinateHyperplaneTwistOrderedBaseCechDifferential
        (R := R) d n =
    OrderedBaseCech.Scheme.Modules.orderedBaseCechDifferential
        (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j d)
        (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) n ≫
      (coordinateHyperplaneTwistOrderedBaseCechObjectIsoUnit
        (R := R) j d (n + 1)).hom := by
  rw [coordinateHyperplaneTwistOrderedBaseCechDifferential,
    OrderedBaseCech.Scheme.Modules.orderedBaseCechDifferential,
    Preadditive.comp_sum, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro k _
  rw [Preadditive.comp_zsmul, Preadditive.zsmul_comp,
    coordinateHyperplaneTwistOrderedBaseCechCoface_naturality]

/-- Consecutive coordinate differentials compose to zero. -/
theorem coordinateHyperplaneTwistOrderedBaseCechDifferential_comp
    [LinearOrder σ] (j : σ) (d : ℤ) (n : ℕ) :
    coordinateHyperplaneTwistOrderedBaseCechDifferential
        (R := R) (σ := σ) d n ≫
      coordinateHyperplaneTwistOrderedBaseCechDifferential
        (R := R) (σ := σ) d (n + 1) = 0 := by
  apply (cancel_epi
    (coordinateHyperplaneTwistOrderedBaseCechObjectIsoUnit
      (R := R) j d n).hom).1
  rw [Limits.comp_zero, ← Category.assoc,
    coordinateHyperplaneTwistOrderedBaseCechDifferential_naturality,
    Category.assoc,
    coordinateHyperplaneTwistOrderedBaseCechDifferential_naturality,
    ← Category.assoc,
    OrderedBaseCech.Scheme.Modules.orderedBaseCechDifferential_comp,
    Limits.zero_comp]

/-- The explicit standard-coordinate ordered Cech complex for `O(d)`. -/
noncomputable def coordinateHyperplaneTwistOrderedBaseCechComplex
    [LinearOrder σ] (j : σ) (d : ℤ) :
    CochainComplex
      (ModuleCat.{u} Γ(Spec (CommRingCat.of R),
        (⊤ : (Spec (CommRingCat.of R)).Opens))) ℕ :=
  CochainComplex.of
    (fun n => OrderedBaseCech.Scheme.Modules.orderedBaseCechObject
      (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      (Invertible.Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
      (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) n)
    (coordinateHyperplaneTwistOrderedBaseCechDifferential
      (R := R) (σ := σ) d)
    (coordinateHyperplaneTwistOrderedBaseCechDifferential_comp
      (R := R) j d)

@[simp]
theorem coordinateHyperplaneTwistOrderedBaseCechComplex_X
    [LinearOrder σ] (j : σ) (d : ℤ) (n : ℕ) :
    (coordinateHyperplaneTwistOrderedBaseCechComplex
      (R := R) j d).X n =
      OrderedBaseCech.Scheme.Modules.orderedBaseCechObject
        (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (Invertible.Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
        (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) n := rfl

@[simp]
theorem coordinateHyperplaneTwistOrderedBaseCechComplex_d
    [LinearOrder σ] (j : σ) (d : ℤ) (n : ℕ) :
    (coordinateHyperplaneTwistOrderedBaseCechComplex
      (R := R) j d).d n (n + 1) =
      coordinateHyperplaneTwistOrderedBaseCechDifferential
        (R := R) (σ := σ) d n := by
  simp [coordinateHyperplaneTwistOrderedBaseCechComplex]

/-- The ordered Cech complex of `O(d)` is the explicit standard-coordinate
complex under the chosen chart frames. -/
noncomputable def coordinateHyperplaneTwistOrderedBaseCechComplexIso
    [LinearOrder σ] (j : σ) (d : ℤ) :
    OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex
        (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j d)
        (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) ≅
      coordinateHyperplaneTwistOrderedBaseCechComplex
        (R := R) j d :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => coordinateHyperplaneTwistOrderedBaseCechObjectIsoUnit
      (R := R) j d n) (by
        intro n m hnm
        simp only [ComplexShape.up_Rel] at hnm
        subst m
        rw [OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex_d,
          coordinateHyperplaneTwistOrderedBaseCechComplex_d]
        exact coordinateHyperplaneTwistOrderedBaseCechDifferential_naturality
          (R := R) j d n)

@[simp]
theorem coordinateHyperplaneTwistOrderedBaseCechComplexIso_hom_f
    [LinearOrder σ] (j : σ) (d : ℤ) (n : ℕ) :
    (coordinateHyperplaneTwistOrderedBaseCechComplexIso
      (R := R) j d).hom.f n =
      (coordinateHyperplaneTwistOrderedBaseCechObjectIsoUnit
        (R := R) j d n).hom := rfl

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistCech.MvPolynomial
