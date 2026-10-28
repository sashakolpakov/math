/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistCechFirstLaurent

/-! # Laurent Cech Data -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.LaurentCechData.MvPolynomial

noncomputable section

open _root_.MvPolynomial

/-!
# Homogeneous Laurent cochain groups and deletion maps

This file reindexes each standard-intersection factor of the existing ordered Cech complex by its
allowed global homogeneous Laurent weights.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace

universe u

variable {R : Type u} {σ : Type} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

local instance : DecidableEq σ := Classical.decEq σ

/-- The degree-`n` coordinate Cech term, with each standard-intersection factor reindexed by the
global degree-`d` homogeneous Laurent weights allowed on its ordered tuple. -/
noncomputable def coordinateHomogeneousLaurentOrderedCechObject
    [LinearOrder σ] (d : ℤ) (n : ℕ) :
    ModuleCat.{u} Γ(Spec (CommRingCat.of R),
      (⊤ : (Spec (CommRingCat.of R)).Opens)) :=
  ∏ᶜ fun a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
    ModuleCat.of
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      (AddMonoidAlgebra
        Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
        {e : LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d //
          e.IsAllowedOn (fun k => (a.1 k).down)})

/-- The existing structure-sheaf coordinate Cech term is factorwise equivalent to its
homogeneous-weight presentation. -/
noncomputable def coordinateHomogeneousLaurentOrderedCechObjectIso
    [LinearOrder σ] (d : ℤ) (n : ℕ) :
    OrderedBaseCech.Scheme.Modules.orderedBaseCechObject
        (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (Invertible.Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
        (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) n ≅
      coordinateHomogeneousLaurentOrderedCechObject (R := R) (σ := σ) d n :=
  Pi.mapIso fun a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
    (StandardCech.MvPolynomial.coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv
      (R := R) a.1 d).toModuleIso

/-- The degreewise homogeneous-weight comparison is the landed factor equivalence on every
ordered tuple. -/
@[reassoc]
theorem coordinateHomogeneousLaurentOrderedCechObjectIso_hom_comp_π
    [LinearOrder σ] (d : ℤ) (n : ℕ)
    (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n) :
    (coordinateHomogeneousLaurentOrderedCechObjectIso
        (R := R) (σ := σ) d n).hom ≫
      Pi.π (fun b : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
        ModuleCat.of
          Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
          (AddMonoidAlgebra
            Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
            {e : LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d //
              e.IsAllowedOn (fun k => (b.1 k).down)})) a =
      Pi.π (fun b : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
        Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor
          (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
          (Invertible.Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
          (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) n b.1) a ≫
        (StandardCech.MvPolynomial.coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv
          (R := R) a.1 d).toModuleIso.hom := by
  exact Pi.mapIso_hom_π
    (fun b : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
      (StandardCech.MvPolynomial.coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv
        (R := R) b.1 d).toModuleIso) a

/-- The ordered Cech coface on homogeneous Laurent weights deletes one entry from the ordered
tuple and extends each allowed weight to the larger intersection. -/
noncomputable def coordinateHomogeneousLaurentOrderedCechCoface
    [LinearOrder σ] (d : ℤ) (n : ℕ) (k : Fin (n + 2)) :
    coordinateHomogeneousLaurentOrderedCechObject (R := R) (σ := σ) d n ⟶
      coordinateHomogeneousLaurentOrderedCechObject (R := R) (σ := σ) d (n + 1) :=
  Pi.lift fun a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1) =>
    Pi.π (fun b : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
      ModuleCat.of
        Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
        (AddMonoidAlgebra
          Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
          {e : LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d //
            e.IsAllowedOn (fun l => (b.1 l).down)})) (a.delete k) ≫
      ModuleCat.ofHom
        (StandardCech.MvPolynomial.coordinateHomogeneousLaurentDeleteLinearMap (R := R) a k d)

/-- Projecting a homogeneous-weight coface to an ordered tuple gives the corresponding deletion
map on allowed weights. -/
@[reassoc]
theorem coordinateHomogeneousLaurentOrderedCechCoface_comp_π
    [LinearOrder σ] (d : ℤ) (n : ℕ) (k : Fin (n + 2))
    (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) :
    coordinateHomogeneousLaurentOrderedCechCoface
        (R := R) (σ := σ) d n k ≫
      Pi.π (fun b : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1) =>
        ModuleCat.of
          Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
          (AddMonoidAlgebra
            Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
            {e : LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d //
              e.IsAllowedOn (fun l => (b.1 l).down)})) a =
      Pi.π (fun b : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
        ModuleCat.of
          Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
          (AddMonoidAlgebra
            Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
            {e : LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d //
              e.IsAllowedOn (fun l => (b.1 l).down)})) (a.delete k) ≫
        ModuleCat.ofHom
          (StandardCech.MvPolynomial.coordinateHomogeneousLaurentDeleteLinearMap (R := R) a k d) := by
  exact Pi.lift_comp_π _ a

/-- On the first face, the homogeneous-weight deletion map is conjugate to restriction followed
by the first-face transition factor. -/
theorem coordinateHomogeneousLaurentFactorCoface_naturality_delete_zero
    [LinearOrder σ] {n : ℕ}
    (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) (d : ℤ) :
    (StandardCech.MvPolynomial.coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv
        (R := R) (a.delete 0).1 d).toModuleIso.hom ≫
      ModuleCat.ofHom
        (StandardCech.MvPolynomial.coordinateHomogeneousLaurentDeleteLinearMap (R := R) a 0 d) =
    (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf
        (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (Invertible.Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))).map
          (StandardCech.MvPolynomial.coordinateOpenCechDelete (R := R) a 0).op ≫
      TwistCechFactors.MvPolynomial.coordinateOpenCechFirstTransitionFactorEnd (R := R) a d ≫
        (StandardCech.MvPolynomial.coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv
          (R := R) a.1 d).toModuleIso.hom := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (TwistCechFirstLaurent.MvPolynomial.coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv_naturality_delete_zero
    (R := R) a d x).symm

/-- On every noninitial face, the homogeneous-weight deletion map is conjugate to ordinary
restriction. -/
theorem coordinateHomogeneousLaurentFactorCoface_naturality_delete_succ
    [LinearOrder σ] {n : ℕ}
    (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (k : Fin (n + 1)) (d : ℤ) :
    (StandardCech.MvPolynomial.coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv
        (R := R) (a.delete k.succ).1 d).toModuleIso.hom ≫
      ModuleCat.ofHom
        (StandardCech.MvPolynomial.coordinateHomogeneousLaurentDeleteLinearMap (R := R) a k.succ d) =
    (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf
        (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (Invertible.Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))).map
          (StandardCech.MvPolynomial.coordinateOpenCechDelete (R := R) a k.succ).op ≫
        (StandardCech.MvPolynomial.coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv
          (R := R) a.1 d).toModuleIso.hom := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (StandardCech.MvPolynomial.coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv_naturality_delete_succ
    (R := R) a k d x).symm

/-- The alternating ordered Cech differential in homogeneous Laurent weights. -/
noncomputable def coordinateHomogeneousLaurentOrderedCechDifferential
    [LinearOrder σ] (d : ℤ) (n : ℕ) :
    coordinateHomogeneousLaurentOrderedCechObject (R := R) (σ := σ) d n ⟶
      coordinateHomogeneousLaurentOrderedCechObject (R := R) (σ := σ) d (n + 1) :=
  ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
    coordinateHomogeneousLaurentOrderedCechCoface (R := R) (σ := σ) d n k

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.LaurentCechData.MvPolynomial
