/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions
import OAI.AlgebraicGeometry.SheafCohomology.Projective.LaurentWeight
import OAI.AlgebraicGeometry.SheafCohomology.Projective.ToSpecZero
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech

/-! # Standard Cech -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial

noncomputable section

open _root_.MvPolynomial

/-!
# Cech factors for twists on polynomial projective space

This file begins the ordered standard-cover calculation of the cohomology of
projective-space twists. It identifies the sections of `O(d)` on each ordered
intersection with the sections of the structure sheaf there.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace

universe u

variable {R : Type u} {σ : Type} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The standard coordinate cover, lifted to the universe of the projective scheme. -/
abbrev coordinateOpenCover (i : ULift.{u} σ) :
    (Proj (homogeneousSubmodule σ R)).Opens :=
  MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i.down

/-- Every member of the universe-lifted standard coordinate cover is affine. -/
theorem coordinateOpenCover_isAffineOpen (i : ULift.{u} σ) :
    IsAffineOpen (coordinateOpenCover (R := R) i) :=
  MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen i.down

/-- The universe-lifted standard coordinate opens cover projective space. -/
theorem iSup_coordinateOpenCover_eq_top :
    ⨆ i : ULift.{u} σ, coordinateOpenCover (R := R) i = ⊤ := by
  apply top_unique
  rw [← MvPolynomialClosure.MvPolynomial.iSup_coordinateOpen_eq_top (R := R)]
  exact iSup_le fun i => le_iSup (coordinateOpenCover (R := R)) (ULift.up i)

/-- The intersection of the standard coordinate charts indexed by a Cech tuple. -/
abbrev coordinateOpenCechIntersection {n : ℕ}
    (a : Fin (n + 1) → ULift.{u} σ) :
    (Proj (homogeneousSubmodule σ R)).Opens :=
  ∏ᶜ fun k : Fin (n + 1) => coordinateOpenCover (R := R) (a k)

/-- A standard Cech intersection is contained in each chart occurring in its tuple. -/
theorem coordinateOpenCechIntersection_le {n : ℕ}
    (a : Fin (n + 1) → ULift.{u} σ)
    (k : Fin (n + 1)) :
    coordinateOpenCechIntersection (R := R) a ≤ coordinateOpenCover (R := R) (a k) :=
  leOfHom (Pi.π (fun l : Fin (n + 1) => coordinateOpenCover (R := R) (a l)) k)

/-- Every finite intersection in the standard coordinate cover is affine. -/
theorem coordinateOpenCechIntersection_isAffineOpen {n : ℕ}
    (a : Fin (n + 1) → ULift.{u} σ) :
    IsAffineOpen (coordinateOpenCechIntersection (R := R) a) := by
  rw [show coordinateOpenCechIntersection (R := R) a =
      ⨅ k : Fin (n + 1), coordinateOpenCover (R := R) (a k) from
    (IsLimit.conePointUniqueUpToIso (limit.isLimit _)
      (Preorder.isLimitIInf _)).to_eq]
  exact IsAffineOpen.iInf fun k => coordinateOpenCover_isAffineOpen (R := R) (a k)

theorem coordinateProductPolynomial_eq_prod {n : ℕ}
    (a : Fin (n + 1) → σ) :
    StandardIntersectionRing.MvPolynomial.coordinateProductPolynomial (R := R) a = ∏ k, X (a k) := by
  classical
  rw [StandardIntersectionRing.MvPolynomial.coordinateProductPolynomial, StandardIntersectionRing.MvPolynomial.coordinateTailPolynomial, Fin.prod_univ_succ]

/-- The coordinate product of a full Cech tuple is the deleted tuple product times the removed
coordinate. -/
theorem coordinateProductPolynomial_eq_delete_mul [LinearOrder σ] {n : ℕ}
    (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (k : Fin (n + 2)) :
    StandardIntersectionRing.MvPolynomial.coordinateProductPolynomial (R := R) (fun l => (a.1 l).down) =
      StandardIntersectionRing.MvPolynomial.coordinateProductPolynomial (R := R) (fun l => ((a.delete k).1 l).down) *
        X (a.1 k).down := by
  classical
  rw [coordinateProductPolynomial_eq_prod, coordinateProductPolynomial_eq_prod,
    Fin.prod_univ_succAbove, mul_comm]
  rfl

/-- Deleting a noninitial Cech coordinate removes exactly that factor from the affine-chart tail
product. -/
theorem coordinateTailPolynomial_eq_delete_succ_mul [LinearOrder σ] {n : ℕ}
    (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (k : Fin (n + 1)) :
    StandardIntersectionRing.MvPolynomial.coordinateTailPolynomial (R := R) (fun l => (a.1 l).down) =
      StandardIntersectionRing.MvPolynomial.coordinateTailPolynomial (R := R)
          (fun l => ((a.delete k.succ).1 l).down) *
        X (a.1 k.succ).down := by
  have h := coordinateProductPolynomial_eq_delete_mul (R := R) a k.succ
  rw [StandardIntersectionRing.MvPolynomial.coordinateProductPolynomial, StandardIntersectionRing.MvPolynomial.coordinateProductPolynomial] at h
  change X (a.1 0).down *
      StandardIntersectionRing.MvPolynomial.coordinateTailPolynomial (R := R) (fun l => (a.1 l).down) =
    (X (a.1 0).down *
      StandardIntersectionRing.MvPolynomial.coordinateTailPolynomial (R := R)
        (fun l => ((a.delete k.succ).1 l).down)) *
      X (a.1 k.succ).down at h
  rw [mul_assoc] at h
  exact X_mul_cancel_left_iff.mp h

/-- For a noninitial deletion, localization first at the deleted tail and then at the removed
coordinate is localization directly at the full tail. -/
theorem coordinateTailAwayMap_comp_delete_succ [LinearOrder σ] {n : ℕ}
    (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (k : Fin (n + 1))
    (q : HomogeneousLocalization.Away
      (homogeneousSubmodule σ R) (X (a.1 0).down)) :
    HomogeneousLocalization.awayMap
        (homogeneousSubmodule σ R)
        (SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one R (a.1 k.succ).down)
        (coordinateProductPolynomial_eq_delete_mul (R := R) a k.succ)
        (HomogeneousLocalization.awayMap
          (homogeneousSubmodule σ R)
          (StandardIntersectionRing.MvPolynomial.coordinateTailPolynomial_mem (R := R)
            (fun l => ((a.delete k.succ).1 l).down))
          (rfl : StandardIntersectionRing.MvPolynomial.coordinateProductPolynomial (R := R)
              (fun l => ((a.delete k.succ).1 l).down) =
            X (a.1 0).down *
              StandardIntersectionRing.MvPolynomial.coordinateTailPolynomial (R := R)
                (fun l => ((a.delete k.succ).1 l).down))
          q) =
      HomogeneousLocalization.awayMap
        (homogeneousSubmodule σ R)
        (StandardIntersectionRing.MvPolynomial.coordinateTailPolynomial_mem (R := R) (fun l => (a.1 l).down))
        (rfl : StandardIntersectionRing.MvPolynomial.coordinateProductPolynomial (R := R) (fun l => (a.1 l).down) =
          X (a.1 0).down *
            StandardIntersectionRing.MvPolynomial.coordinateTailPolynomial (R := R) (fun l => (a.1 l).down))
        q := by
  have hy' : StandardIntersectionRing.MvPolynomial.coordinateProductPolynomial (R := R) (fun l => (a.1 l).down) =
      X (a.1 0).down *
        (StandardIntersectionRing.MvPolynomial.coordinateTailPolynomial (R := R)
          (fun l => ((a.delete k.succ).1 l).down) * X (a.1 k.succ).down) := by
    rw [StandardIntersectionRing.MvPolynomial.coordinateProductPolynomial, coordinateTailPolynomial_eq_delete_succ_mul]
  have h := congrArg
    (fun f : HomogeneousLocalization.Away
        (homogeneousSubmodule σ R) (X (a.1 0).down) →+*
        HomogeneousLocalization.Away (homogeneousSubmodule σ R)
          (StandardIntersectionRing.MvPolynomial.coordinateProductPolynomial (R := R) (fun l => (a.1 l).down)) => f q)
    (StandardIntersectionRing.HomogeneousLocalization.awayMap_comp
      (homogeneousSubmodule σ R)
      (SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one R (a.1 0).down)
      (StandardIntersectionRing.MvPolynomial.coordinateTailPolynomial_mem (R := R)
        (fun l => ((a.delete k.succ).1 l).down))
      (SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one R (a.1 k.succ).down)
      (rfl : StandardIntersectionRing.MvPolynomial.coordinateProductPolynomial (R := R)
          (fun l => ((a.delete k.succ).1 l).down) =
        X (a.1 0).down *
          StandardIntersectionRing.MvPolynomial.coordinateTailPolynomial (R := R)
            (fun l => ((a.delete k.succ).1 l).down))
      (coordinateProductPolynomial_eq_delete_mul (R := R) a k.succ)
      hy')
  rw [RingHom.comp_apply] at h
  exact h

theorem basicOpen_prod {ι : Type*} [Fintype ι]
    (f : ι → MvPolynomial σ R) :
    Proj.basicOpen (homogeneousSubmodule σ R) (∏ i, f i) =
      ⨅ i, Proj.basicOpen (homogeneousSubmodule σ R) (f i) := by
  classical
  ext x
  rw [TopologicalSpace.Opens.coe_iInf]
  simp only [Set.mem_iInter]
  let y : ProjectiveSpectrum (homogeneousSubmodule σ R) := x
  change (∏ i, f i) ∉ y.asHomogeneousIdeal.toIdeal ↔
    ∀ i, f i ∉ y.asHomogeneousIdeal.toIdeal
  have hprod : (∏ i, f i) ∈ y.asHomogeneousIdeal.toIdeal ↔
      ∃ i, f i ∈ y.asHomogeneousIdeal.toIdeal := by
    simpa using (Ideal.IsPrime.prod_mem_iff
      (s := Finset.univ) (x := f) (p := y.asHomogeneousIdeal.toIdeal))
  rw [not_congr hprod]
  simp

/-- A standard Cech intersection is the single basic open at its tuple coordinate product. -/
theorem coordinateOpenCechIntersection_eq_basicOpen {n : ℕ}
    (a : Fin (n + 1) → ULift.{u} σ) :
    coordinateOpenCechIntersection (R := R) a =
      Proj.basicOpen (homogeneousSubmodule σ R)
        (StandardIntersectionRing.MvPolynomial.coordinateProductPolynomial (R := R) (fun k => (a k).down)) := by
  rw [show coordinateOpenCechIntersection (R := R) a =
      ⨅ k : Fin (n + 1), coordinateOpenCover (R := R) (a k) from
    (IsLimit.conePointUniqueUpToIso (limit.isLimit _)
      (Preorder.isLimitIInf _)).to_eq]
  rw [coordinateProductPolynomial_eq_prod]
  exact (basicOpen_prod (R := R) (fun k : Fin (n + 1) => X (a k).down)).symm

/-- The canonical homogeneous localization presentation of a standard Cech intersection's
structure-sheaf sections. -/
noncomputable def coordinateOpenCechIntersectionAwayIso {n : ℕ}
    (a : Fin (n + 1) → ULift.{u} σ) :
    CommRingCat.of
        (HomogeneousLocalization.Away (homogeneousSubmodule σ R)
          (StandardIntersectionRing.MvPolynomial.coordinateProductPolynomial (R := R) (fun k => (a k).down))) ≅
      Γ(Proj (homogeneousSubmodule σ R), coordinateOpenCechIntersection (R := R) a) :=
  (Proj.basicOpenIsoAway (homogeneousSubmodule σ R)
      (StandardIntersectionRing.MvPolynomial.coordinateProductPolynomial (R := R) (fun k => (a k).down))
      (StandardIntersectionRing.MvPolynomial.coordinateProductPolynomial_mem (R := R) (fun k => (a k).down))
      (Nat.succ_pos n)).trans
    ((Proj (homogeneousSubmodule σ R)).presheaf.mapIso
      (eqToIso (coordinateOpenCechIntersection_eq_basicOpen (R := R) a)).op)

/-- Sections on a standard projective Cech intersection, in Laurent-monomial coordinates. -/
noncomputable def coordinateOpenCechIntersectionLaurentRingEquiv {n : ℕ}
    (a : Fin (n + 1) → ULift.{u} σ) :
    Γ(Proj (homogeneousSubmodule σ R),
        coordinateOpenCechIntersection (R := R) a) ≃+*
      AddMonoidAlgebra R
        (LaurentExponentLocalization.MvPolynomial.laurentExponentSubmonoid
          (StandardIntersectionRing.MvPolynomial.coordinateTailExponent (fun k => (a k).down))) :=
  (coordinateOpenCechIntersectionAwayIso (R := R) a).commRingCatIsoToRingEquiv.symm |>.trans
    ((StandardIntersectionRing.MvPolynomial.coordinateProductAwayRingEquiv (R := R) (fun k => (a k).down)).trans
      (LaurentMonomialBasis.MvPolynomial.laurentMonomialRingEquiv R
        (StandardIntersectionRing.MvPolynomial.coordinateTailExponent (fun k => (a k).down))))

/-- Laurent-monomial coordinates with coefficients transported to the global sections of the
affine base. -/
noncomputable def coordinateOpenCechIntersectionBaseLaurentRingEquiv {n : ℕ}
    (a : Fin (n + 1) → ULift.{u} σ) :
    Γ(Proj (homogeneousSubmodule σ R),
        coordinateOpenCechIntersection (R := R) a) ≃+*
      AddMonoidAlgebra Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
        (LaurentExponentLocalization.MvPolynomial.laurentExponentSubmonoid
          (StandardIntersectionRing.MvPolynomial.coordinateTailExponent (fun k => (a k).down))) :=
  (coordinateOpenCechIntersectionLaurentRingEquiv (R := R) a).trans
    (AddMonoidAlgebra.mapRingEquiv _
      (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm)

/-- The structure morphism on a projective Cech intersection is the coefficient map into its
homogeneous localization presentation. -/
theorem coordinateOpenCechIntersection_structure_section_square {n : ℕ}
    (a : Fin (n + 1) → ULift.{u} σ) :
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
        (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)).appTop ≫
        (Proj (homogeneousSubmodule σ R)).presheaf.map (homOfLE le_top).op ≫
        (coordinateOpenCechIntersectionAwayIso (R := R) a).inv =
      CommRingCat.ofHom
        (StandardIntersectionRing.MvPolynomial.homogeneousAwayCoeffHom
          (StandardIntersectionRing.MvPolynomial.coordinateProductPolynomial (R := R) (fun k => (a k).down))) := by
  simp only [coordinateOpenCechIntersectionAwayIso, Iso.trans_inv,
    Functor.mapIso_inv]
  rw [← Category.assoc
    ((Proj (homogeneousSubmodule σ R)).presheaf.map (homOfLE le_top).op)]
  rw [← Functor.map_comp]
  rw [show (homOfLE le_top).op ≫
      (eqToIso (coordinateOpenCechIntersection_eq_basicOpen (R := R) a)).op.inv =
        (homOfLE le_top).op from Subsingleton.elim _ _]
  simpa [MvPolynomialClosure.MvPolynomial.homogeneousProjπ, StandardIntersectionRing.MvPolynomial.homogeneousAwayCoeffHom] using
    (ToSpecZero.Proj_structure_section_square
      (homogeneousSubmodule σ R)
      (algebraMap R (homogeneousSubmodule σ R 0))
      (StandardIntersectionRing.MvPolynomial.coordinateProductPolynomial (R := R) (fun k => (a k).down))
      (StandardIntersectionRing.MvPolynomial.coordinateProductPolynomial_mem (R := R) (fun k => (a k).down))
      (Nat.succ_pos n))

/-- The base scalar map into a projective Cech intersection in homogeneous-localization
coordinates. -/
theorem coordinateOpenCechIntersection_baseScalarHom {n : ℕ}
    (a : Fin (n + 1) → ULift.{u} σ) :
    (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)).appTop ≫
        (Proj (homogeneousSubmodule σ R)).presheaf.map (homOfLE le_top).op ≫
        (coordinateOpenCechIntersectionAwayIso (R := R) a).inv =
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫
        CommRingCat.ofHom
          (StandardIntersectionRing.MvPolynomial.homogeneousAwayCoeffHom
            (StandardIntersectionRing.MvPolynomial.coordinateProductPolynomial (R := R) (fun k => (a k).down))) := by
  rw [← Iso.inv_comp_eq]
  exact coordinateOpenCechIntersection_structure_section_square (R := R) a

/-- A base scalar is the constant Laurent monomial in coefficient-ring coordinates. -/
@[simp]
theorem coordinateOpenCechIntersectionLaurentRingEquiv_baseScalar {n : ℕ}
    (a : Fin (n + 1) → ULift.{u} σ)
    (r : Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))) :
    coordinateOpenCechIntersectionLaurentRingEquiv (R := R) a
        (((Proj (homogeneousSubmodule σ R)).presheaf.map
          (homOfLE le_top).op).hom
            ((MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)).appTop.hom r)) =
      AddMonoidAlgebra.single 0
        ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r) := by
  change LaurentMonomialBasis.MvPolynomial.laurentMonomialRingEquiv R _
      (StandardIntersectionRing.MvPolynomial.coordinateProductAwayRingEquiv (R := R) _
        ((coordinateOpenCechIntersectionAwayIso (R := R) a).inv.hom
          (((Proj (homogeneousSubmodule σ R)).presheaf.map
            (homOfLE le_top).op).hom
              ((MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)).appTop.hom r)))) = _
  have hscalar := congrArg
    (fun q : Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens)) →+*
        HomogeneousLocalization.Away (homogeneousSubmodule σ R)
          (StandardIntersectionRing.MvPolynomial.coordinateProductPolynomial (R := R) (fun k => (a k).down)) => q r)
    (congrArg CommRingCat.Hom.hom
      (coordinateOpenCechIntersection_baseScalarHom (R := R) a))
  change (coordinateOpenCechIntersectionAwayIso (R := R) a).inv.hom
      (((Proj (homogeneousSubmodule σ R)).presheaf.map
        (homOfLE le_top).op).hom
          ((MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)).appTop.hom r)) =
    algebraMap R
      (HomogeneousLocalization.Away (homogeneousSubmodule σ R)
        (StandardIntersectionRing.MvPolynomial.coordinateProductPolynomial (R := R) (fun k => (a k).down)))
      ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r) at hscalar
  rw [hscalar, StandardIntersectionRing.MvPolynomial.coordinateProductAwayRingEquiv_algebraMap,
    LaurentMonomialBasis.MvPolynomial.laurentMonomialRingEquiv_algebraMap_coeff]
  rfl

/-- A base scalar is the constant Laurent monomial after transporting coefficients to the affine
base's global-section ring. -/
@[simp]
theorem coordinateOpenCechIntersectionBaseLaurentRingEquiv_baseScalar {n : ℕ}
    (a : Fin (n + 1) → ULift.{u} σ)
    (r : Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))) :
    coordinateOpenCechIntersectionBaseLaurentRingEquiv (R := R) a
        (((Proj (homogeneousSubmodule σ R)).presheaf.map
          (homOfLE le_top).op).hom
            ((MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)).appTop.hom r)) =
      algebraMap
        Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
        (AddMonoidAlgebra
          Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
          (LaurentExponentLocalization.MvPolynomial.laurentExponentSubmonoid
            (StandardIntersectionRing.MvPolynomial.coordinateTailExponent (fun k => (a k).down)))) r := by
  change AddMonoidAlgebra.mapRingEquiv _
      (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm
        (coordinateOpenCechIntersectionLaurentRingEquiv (R := R) a
          (((Proj (homogeneousSubmodule σ R)).presheaf.map
            (homOfLE le_top).op).hom
              ((MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)).appTop.hom r))) = _
  rw [coordinateOpenCechIntersectionLaurentRingEquiv_baseScalar,
    AddMonoidAlgebra.mapRingEquiv_single]
  change AddMonoidAlgebra.single 0
      ((Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm
        ((Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv r)) =
    AddMonoidAlgebra.single 0 r
  rw [(Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm_apply_apply]

noncomputable def coordinateOpenCechIntersectionBaseCechFactorAddEquiv {n : ℕ}
    (a : Fin (n + 1) → ULift.{u} σ) :
    Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor
        (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (Invertible.Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
        (coordinateOpenCover (R := R) (σ := σ)) n a ≃+
      Γ(Proj (homogeneousSubmodule σ R),
        coordinateOpenCechIntersection (R := R) a) :=
  AddEquiv.refl _

theorem coordinateOpenCechIntersectionBaseCechFactorAddEquiv_smul {n : ℕ}
    (a : Fin (n + 1) → ULift.{u} σ)
    (r : Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens)))
    (x : Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor
        (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (Invertible.Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
        (coordinateOpenCover (R := R) (σ := σ)) n a) :
    coordinateOpenCechIntersectionBaseCechFactorAddEquiv (R := R) a (r • x) =
      ((Proj (homogeneousSubmodule σ R)).presheaf.map
        (homOfLE (show coordinateOpenCechIntersection (R := R) a ≤ ⊤ from
          le_top)).op).hom
          ((MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)).appTop.hom r) *
        coordinateOpenCechIntersectionBaseCechFactorAddEquiv (R := R) a x := by
  rfl

/-- A standard projective Cech intersection factor is the free module on its allowed Laurent
monomials over the affine base's global-section ring. -/
noncomputable def coordinateOpenCechIntersectionBaseLaurentLinearEquiv {n : ℕ}
    (a : Fin (n + 1) → ULift.{u} σ) :
    Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor
        (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (Invertible.Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
        (coordinateOpenCover (R := R) (σ := σ)) n a ≃ₗ[
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))]
      AddMonoidAlgebra
        Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
        (LaurentExponentLocalization.MvPolynomial.laurentExponentSubmonoid
          (StandardIntersectionRing.MvPolynomial.coordinateTailExponent (fun k => (a k).down))) :=
  { (coordinateOpenCechIntersectionBaseCechFactorAddEquiv (R := R) a).trans
      (coordinateOpenCechIntersectionBaseLaurentRingEquiv (R := R) a).toAddEquiv with
    map_smul' := by
      intro r x
      change coordinateOpenCechIntersectionBaseLaurentRingEquiv (R := R) a
          (coordinateOpenCechIntersectionBaseCechFactorAddEquiv (R := R) a (r • x)) =
        r • coordinateOpenCechIntersectionBaseLaurentRingEquiv (R := R) a
          (coordinateOpenCechIntersectionBaseCechFactorAddEquiv (R := R) a x)
      rw [coordinateOpenCechIntersectionBaseCechFactorAddEquiv_smul]
      rw [map_mul,
        coordinateOpenCechIntersectionBaseLaurentRingEquiv_baseScalar]
      rw [Algebra.smul_def] }

/-- A standard projective Cech intersection factor, reindexed by global homogeneous Laurent
weights of total degree `d` allowed on its coordinate tuple. -/
noncomputable def coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv {n : ℕ}
    (a : Fin (n + 1) → ULift.{u} σ) (d : ℤ) :
    Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor
        (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (Invertible.Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
        (coordinateOpenCover (R := R) (σ := σ)) n a ≃ₗ[
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))]
      AddMonoidAlgebra
        Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
        {e : LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d //
          e.IsAllowedOn (fun k => (a k).down)} :=
  (coordinateOpenCechIntersectionBaseLaurentLinearEquiv (R := R) a).trans
    (AddMonoidAlgebra.mapDomainLinearEquiv
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      (LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv (fun k => (a k).down) d))

/-- The homogeneous-weight factor equivalence sends a local Laurent basis vector to the same
monomial indexed by its global weight. -/
@[simp]
theorem coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv_basis_apply
    {n : ℕ} (a : Fin (n + 1) → ULift.{u} σ) (d : ℤ)
    (e : LaurentExponentLocalization.MvPolynomial.laurentExponentSubmonoid
      (StandardIntersectionRing.MvPolynomial.coordinateTailExponent (fun k => (a k).down)))
    (r : Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))) :
    coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv (R := R) a d
        ((coordinateOpenCechIntersectionBaseLaurentLinearEquiv (R := R) a).symm
          (AddMonoidAlgebra.single e r)) =
      AddMonoidAlgebra.single
        (LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv (fun k => (a k).down) d e) r := by
  rw [coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv,
    LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    AddMonoidAlgebra.mapDomainLinearEquiv_single]

/-- Deleting a Cech coordinate can only shrink the tuple, so every weight allowed on the deleted
tuple is allowed on the full tuple. -/
def coordinateLaurentExponentDeleteEmbedding [LinearOrder σ] {n : ℕ}
    (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (k : Fin (n + 2)) (d : ℤ) :
    {e : LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d //
        e.IsAllowedOn (fun l => ((a.delete k).1 l).down)} ↪
      {e : LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d //
        e.IsAllowedOn (fun l => (a.1 l).down)} where
  toFun e := ⟨e.1, by
    intro i hi
    obtain ⟨l, hl⟩ := e.2 hi
    refine ⟨k.succAbove l, ?_⟩
    change (a.1 (k.succAbove l)).down = i at hl
    exact hl⟩
  inj' e f h := by
    apply Subtype.ext
    exact congrArg
      (fun x : {e : LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d //
        e.IsAllowedOn (fun l => (a.1 l).down)} => x.1) h

/-- The weight-coordinate form of a Cech coface: include the weights allowed on the deleted tuple
among those allowed on the full tuple. -/
noncomputable def coordinateHomogeneousLaurentDeleteLinearMap [LinearOrder σ] {n : ℕ}
    (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (k : Fin (n + 2)) (d : ℤ) :
    AddMonoidAlgebra
        Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
        {e : LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d //
          e.IsAllowedOn (fun l => ((a.delete k).1 l).down)} →ₗ[
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))]
      AddMonoidAlgebra
        Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
        {e : LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d //
          e.IsAllowedOn (fun l => (a.1 l).down)} :=
  AddMonoidAlgebra.mapDomainLinearMap
    Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
    Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
    (coordinateLaurentExponentDeleteEmbedding a k d)

/-- A Cech deletion map preserves the underlying global homogeneous weight. -/
@[simp]
theorem coordinateHomogeneousLaurentDeleteLinearMap_single [LinearOrder σ] {n : ℕ}
    (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (k : Fin (n + 2)) (d : ℤ)
    (e : {e : LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d //
      e.IsAllowedOn (fun l => ((a.delete k).1 l).down)})
    (r : Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))) :
    coordinateHomogeneousLaurentDeleteLinearMap (R := R) a k d
        (AddMonoidAlgebra.single e r) =
      AddMonoidAlgebra.single (coordinateLaurentExponentDeleteEmbedding a k d e) r := by
  exact AddMonoidAlgebra.mapDomainLinearMap_single
    (R := Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens)))
    (S := Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens)))
    (coordinateLaurentExponentDeleteEmbedding a k d) r e

/-- For a noninitial deletion, a local Laurent exponent remains the same exponent and only gains
the enlarged support permission from the full tuple. -/
noncomputable def coordinateLaurentExponentDeleteAddMonoidHom [LinearOrder σ] {n : ℕ}
    (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (k : Fin (n + 1)) :
    LaurentExponentLocalization.MvPolynomial.laurentExponentSubmonoid
        (StandardIntersectionRing.MvPolynomial.coordinateTailExponent (fun l => ((a.delete k.succ).1 l).down)) →+
      LaurentExponentLocalization.MvPolynomial.laurentExponentSubmonoid
        (StandardIntersectionRing.MvPolynomial.coordinateTailExponent (fun l => (a.1 l).down)) where
  toFun e := ⟨e.1, by
    intro i hi
    apply (StandardIntersectionRing.MvPolynomial.coordinateTailExponent_ne_zero_iff
      (fun l => (a.1 l).down) i).2
    obtain ⟨l, hl⟩ := (StandardIntersectionRing.MvPolynomial.coordinateTailExponent_ne_zero_iff
      (fun l => ((a.delete k.succ).1 l).down) i).1 (e.2 i hi)
    exact ⟨k.succ.succAbove l, hl⟩⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The local exponent inclusion commutes with the natural-exponent maps into the two Laurent
localizations. -/
theorem coordinateLaurentExponentDeleteAddMonoidHom_awayMap [LinearOrder σ] {n : ℕ}
    (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (k : Fin (n + 1))
    (e : {j : σ // j ≠ (a.1 0).down} →₀ ℕ) :
    coordinateLaurentExponentDeleteAddMonoidHom a k
        (LaurentExponentLocalization.MvPolynomial.laurentExponentAwayMap
          (StandardIntersectionRing.MvPolynomial.coordinateTailExponent
            (fun l => ((a.delete k.succ).1 l).down)) e) =
      LaurentExponentLocalization.MvPolynomial.laurentExponentAwayMap
        (StandardIntersectionRing.MvPolynomial.coordinateTailExponent (fun l => (a.1 l).down)) e := by
  apply Subtype.ext
  ext i
  rfl

/-- Reindexing local exponents by homogeneous weights identifies the noninitial local inclusion
with the global deleted-tuple inclusion. -/
theorem coordinateLaurentExponentEquiv_delete_succ [LinearOrder σ] {n : ℕ}
    (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (k : Fin (n + 1)) (d : ℤ)
    (e : LaurentExponentLocalization.MvPolynomial.laurentExponentSubmonoid
      (StandardIntersectionRing.MvPolynomial.coordinateTailExponent (fun l => ((a.delete k.succ).1 l).down))) :
    LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv (fun l => (a.1 l).down) d
        (coordinateLaurentExponentDeleteAddMonoidHom a k e) =
      coordinateLaurentExponentDeleteEmbedding a k.succ d
        (LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv
          (fun l => ((a.delete k.succ).1 l).down) d e) := by
  apply Subtype.ext
  apply Subtype.ext
  ext i
  change (LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv (fun l => (a.1 l).down) d
      (coordinateLaurentExponentDeleteAddMonoidHom a k e)).1.1 i =
    (LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv
      (fun l => ((a.delete k.succ).1 l).down) d e).1.1 i
  have hanchor : ((a.delete k.succ).1 0).down = (a.1 0).down := rfl
  by_cases hi : i = (a.1 0).down
  · subst i
    rw [LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv_apply_anchor]
    change d - Finsupp.degree e.1 =
      (LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv
        (fun l => ((a.delete k.succ).1 l).down) d e).1.1
          ((a.delete k.succ).1 0).down
    exact (LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv_apply_anchor
      (fun l => ((a.delete k.succ).1 l).down) d e).symm
  · have hi' : i ≠ ((a.delete k.succ).1 0).down := by
      simpa [hanchor] using hi
    rw [LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv_apply_of_ne _ _ _ _ hi,
      LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv_apply_of_ne _ _ _ _ hi']
    rfl

local instance : DecidableEq σ := Classical.decEq σ

theorem coordinateLaurentExponentDeleteRingHom_comp [LinearOrder σ] {n : ℕ}
    (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (k : Fin (n + 1)) :
    (AddMonoidAlgebra.mapDomainRingHom R
      (coordinateLaurentExponentDeleteAddMonoidHom a k)).comp
        (AddMonoidAlgebra.mapDomainRingHom R
          (LaurentExponentLocalization.MvPolynomial.laurentExponentAwayMap
            (StandardIntersectionRing.MvPolynomial.coordinateTailExponent
              (fun l => ((a.delete k.succ).1 l).down))).toAddMonoidHom) =
      AddMonoidAlgebra.mapDomainRingHom R
        (LaurentExponentLocalization.MvPolynomial.laurentExponentAwayMap
          (StandardIntersectionRing.MvPolynomial.coordinateTailExponent (fun l => (a.1 l).down))).toAddMonoidHom := by
  rw [← AddMonoidAlgebra.mapDomainRingHom_comp]
  congr 1

/-- For a noninitial deletion, Laurent coordinates identify restriction to the full ordered Cech
intersection with the inclusion that preserves the underlying Laurent exponent. -/
theorem coordinateProductAwayLaurentRingEquiv_naturality_delete_succ
    [LinearOrder σ] {n : ℕ}
    (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (k : Fin (n + 1)) :
    (LaurentMonomialBasis.MvPolynomial.laurentMonomialRingEquiv R
        (StandardIntersectionRing.MvPolynomial.coordinateTailExponent (fun l => (a.1 l).down))).toRingHom.comp
        ((StandardIntersectionRing.MvPolynomial.coordinateProductAwayRingEquiv (R := R)
          (fun l => (a.1 l).down)).toRingHom.comp
          (HomogeneousLocalization.awayMap
            (homogeneousSubmodule σ R)
            (SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one R (a.1 k.succ).down)
            (coordinateProductPolynomial_eq_delete_mul (R := R) a k.succ))) =
      (AddMonoidAlgebra.mapDomainRingHom R
        (coordinateLaurentExponentDeleteAddMonoidHom a k)).comp
        ((LaurentMonomialBasis.MvPolynomial.laurentMonomialRingEquiv R
          (StandardIntersectionRing.MvPolynomial.coordinateTailExponent
            (fun l => ((a.delete k.succ).1 l).down))).toRingHom.comp
          (StandardIntersectionRing.MvPolynomial.coordinateProductAwayRingEquiv (R := R)
            (fun l => ((a.delete k.succ).1 l).down)).toRingHom) := by
  let := (HomogeneousLocalization.awayMap
    (f := X (a.1 0).down)
    (g := StandardIntersectionRing.MvPolynomial.coordinateTailPolynomial (R := R)
      (fun l => ((a.delete k.succ).1 l).down))
    (x := StandardIntersectionRing.MvPolynomial.coordinateProductPolynomial (R := R)
      (fun l => ((a.delete k.succ).1 l).down))
    (homogeneousSubmodule σ R)
    (StandardIntersectionRing.MvPolynomial.coordinateTailPolynomial_mem (R := R)
      (fun l => ((a.delete k.succ).1 l).down)) rfl).toAlgebra
  let t : HomogeneousLocalization.Away (homogeneousSubmodule σ R)
      (X (a.1 0).down) :=
    HomogeneousLocalization.Away.isLocalizationElem
      (SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one R (a.1 0).down)
      (StandardIntersectionRing.MvPolynomial.coordinateTailPolynomial_mem (R := R)
        (fun l => ((a.delete k.succ).1 l).down))
  let : IsLocalization.Away t
      (HomogeneousLocalization.Away (homogeneousSubmodule σ R)
        (StandardIntersectionRing.MvPolynomial.coordinateProductPolynomial (R := R)
          (fun l => ((a.delete k.succ).1 l).down))) :=
    HomogeneousLocalization.Away.isLocalization_mul
      (SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one R (a.1 0).down)
      (StandardIntersectionRing.MvPolynomial.coordinateTailPolynomial_mem (R := R)
        (fun l => ((a.delete k.succ).1 l).down)) rfl one_ne_zero
  apply IsLocalization.ringHom_ext (Submonoid.powers t)
  apply DFunLike.ext _ _
  intro q
  simp only [RingHom.comp_apply]
  rw [show algebraMap
      (HomogeneousLocalization.Away (homogeneousSubmodule σ R) (X (a.1 0).down))
      (HomogeneousLocalization.Away (homogeneousSubmodule σ R)
        (StandardIntersectionRing.MvPolynomial.coordinateProductPolynomial (R := R)
          (fun l => ((a.delete k.succ).1 l).down))) q =
    HomogeneousLocalization.awayMap
      (f := X (a.1 0).down)
      (g := StandardIntersectionRing.MvPolynomial.coordinateTailPolynomial (R := R)
        (fun l => ((a.delete k.succ).1 l).down))
      (x := StandardIntersectionRing.MvPolynomial.coordinateProductPolynomial (R := R)
        (fun l => ((a.delete k.succ).1 l).down))
      (homogeneousSubmodule σ R)
      (StandardIntersectionRing.MvPolynomial.coordinateTailPolynomial_mem (R := R)
        (fun l => ((a.delete k.succ).1 l).down)) rfl q from rfl]
  let p := SpaceChart.MvPolynomial.chartRingEquiv R (a.1 0).down q
  calc
    _ = LaurentMonomialBasis.MvPolynomial.laurentMonomialRingEquiv R
        (StandardIntersectionRing.MvPolynomial.coordinateTailExponent (fun l => (a.1 l).down))
        (StandardIntersectionRing.MvPolynomial.coordinateProductAwayRingEquiv (R := R) (fun l => (a.1 l).down)
          (HomogeneousLocalization.awayMap
            (f := X (a.1 0).down)
            (g := StandardIntersectionRing.MvPolynomial.coordinateTailPolynomial (R := R) (fun l => (a.1 l).down))
            (x := StandardIntersectionRing.MvPolynomial.coordinateProductPolynomial (R := R) (fun l => (a.1 l).down))
            (homogeneousSubmodule σ R)
            (StandardIntersectionRing.MvPolynomial.coordinateTailPolynomial_mem (R := R)
              (fun l => (a.1 l).down)) rfl q)) := congrArg
              (fun x => LaurentMonomialBasis.MvPolynomial.laurentMonomialRingEquiv R
                (StandardIntersectionRing.MvPolynomial.coordinateTailExponent (fun l => (a.1 l).down))
                (StandardIntersectionRing.MvPolynomial.coordinateProductAwayRingEquiv (R := R)
                  (fun l => (a.1 l).down) x))
              (coordinateTailAwayMap_comp_delete_succ (R := R) a k q)
    _ = AddMonoidAlgebra.mapDomain
        (LaurentExponentLocalization.MvPolynomial.laurentExponentAwayMap
          (StandardIntersectionRing.MvPolynomial.coordinateTailExponent (fun l => (a.1 l).down))).toAddMonoidHom p :=
      StandardIntersectionRing.MvPolynomial.coordinateProductAwayLaurentRingEquiv_awayMap
        (R := R) (σ := σ) (n := n + 1) (fun l => (a.1 l).down) q
    _ = AddMonoidAlgebra.mapDomain
        (coordinateLaurentExponentDeleteAddMonoidHom a k)
        (AddMonoidAlgebra.mapDomain
          (LaurentExponentLocalization.MvPolynomial.laurentExponentAwayMap
            (StandardIntersectionRing.MvPolynomial.coordinateTailExponent
              (fun l => ((a.delete k.succ).1 l).down))).toAddMonoidHom p) := by
      change (AddMonoidAlgebra.mapDomainRingHom R
          (LaurentExponentLocalization.MvPolynomial.laurentExponentAwayMap
            (StandardIntersectionRing.MvPolynomial.coordinateTailExponent (fun l => (a.1 l).down))).toAddMonoidHom) p =
        ((AddMonoidAlgebra.mapDomainRingHom R
          (coordinateLaurentExponentDeleteAddMonoidHom a k)).comp
          (AddMonoidAlgebra.mapDomainRingHom R
            (LaurentExponentLocalization.MvPolynomial.laurentExponentAwayMap
              (StandardIntersectionRing.MvPolynomial.coordinateTailExponent
                (fun l => ((a.delete k.succ).1 l).down))).toAddMonoidHom)) p
      exact congrArg (fun f => f p)
        (coordinateLaurentExponentDeleteRingHom_comp (R := R) a k).symm
    _ = _ := congrArg
      (AddMonoidAlgebra.mapDomain
        (coordinateLaurentExponentDeleteAddMonoidHom a k))
      (StandardIntersectionRing.MvPolynomial.coordinateProductAwayLaurentRingEquiv_awayMap
        (R := R) (σ := σ) (n := n)
        (fun l => ((a.delete k.succ).1 l).down) q).symm

/-- The inclusion of a full ordered Cech intersection into the intersection obtained by deleting
one entry. -/
abbrev coordinateOpenCechDelete [LinearOrder σ] {n : ℕ}
    (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (k : Fin (n + 2)) :
    coordinateOpenCechIntersection (R := R) a.1 ⟶
      coordinateOpenCechIntersection (R := R) (a.delete k).1 :=
  (((FormalCoproduct.mk _ (coordinateOpenCover (R := R) (σ := σ))).mapPower
    (SimplexCategory.δ k).toOrderHom.toFun).φ a.1)

/-- Restriction from a deleted Cech intersection to the full intersection is the homogeneous
localization map at the removed coordinate. -/
theorem coordinateOpenCechIntersectionAwayIso_naturality_delete [LinearOrder σ] {n : ℕ}
    (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (k : Fin (n + 2)) :
    CommRingCat.ofHom
        (HomogeneousLocalization.awayMap
          (homogeneousSubmodule σ R)
          (SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one R (a.1 k).down)
          (coordinateProductPolynomial_eq_delete_mul (R := R) a k)) ≫
      (coordinateOpenCechIntersectionAwayIso (R := R) a.1).hom =
    (coordinateOpenCechIntersectionAwayIso (R := R) (a.delete k).1).hom ≫
      (Proj (homogeneousSubmodule σ R)).presheaf.map
        (coordinateOpenCechDelete (R := R) a k).op := by
  simp only [coordinateOpenCechIntersectionAwayIso, Iso.trans_hom,
    Functor.mapIso_hom, Proj.basicOpenIsoAway, asIso_hom]
  rw [← Category.assoc, Proj.awayMap_awayToSection]
  simp only [Category.assoc]
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

/-- Restriction from the first standard chart to a full Cech intersection is the homogeneous
localization map at the product of the remaining coordinates. -/
theorem coordinateOpenCechIntersectionAwayIso_naturality_firstChart {n : ℕ}
    (a : Fin (n + 1) → ULift.{u} σ) :
    CommRingCat.ofHom
        (HomogeneousLocalization.awayMap
          (f := X (a 0).down)
          (g := StandardIntersectionRing.MvPolynomial.coordinateTailPolynomial (R := R) (fun k => (a k).down))
          (x := StandardIntersectionRing.MvPolynomial.coordinateProductPolynomial (R := R) (fun k => (a k).down))
          (homogeneousSubmodule σ R)
          (StandardIntersectionRing.MvPolynomial.coordinateTailPolynomial_mem (R := R) (fun k => (a k).down))
          (show StandardIntersectionRing.MvPolynomial.coordinateProductPolynomial (R := R) (fun k => (a k).down) =
            X (a 0).down * StandardIntersectionRing.MvPolynomial.coordinateTailPolynomial (R := R) (fun k => (a k).down)
            by rw [StandardIntersectionRing.MvPolynomial.coordinateProductPolynomial])) ≫
      (coordinateOpenCechIntersectionAwayIso (R := R) a).hom =
    (Proj.basicOpenIsoAway (homogeneousSubmodule σ R) (X (a 0).down)
        (SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one R (a 0).down) one_pos).hom ≫
      (Proj (homogeneousSubmodule σ R)).presheaf.map
        (homOfLE (coordinateOpenCechIntersection_le (R := R) a 0)).op := by
  simp only [coordinateOpenCechIntersectionAwayIso, Iso.trans_hom,
    Functor.mapIso_hom, Proj.basicOpenIsoAway, asIso_hom]
  rw [← Category.assoc, Proj.awayMap_awayToSection]
  simp only [Category.assoc]
  rw [← Functor.map_comp]
  congr 1

/-- Laurent coordinates carry noninitial restriction between standard Cech intersections to the
inclusion that preserves the underlying local exponent. -/
theorem coordinateOpenCechIntersectionLaurentRingEquiv_naturality_delete_succ
    [LinearOrder σ] {n : ℕ}
    (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (k : Fin (n + 1))
    (x : Γ(Proj (homogeneousSubmodule σ R),
      coordinateOpenCechIntersection (R := R) (a.delete k.succ).1)) :
    coordinateOpenCechIntersectionLaurentRingEquiv (R := R) a.1
        ((Proj (homogeneousSubmodule σ R)).presheaf.map
          (coordinateOpenCechDelete (R := R) a k.succ).op x) =
      AddMonoidAlgebra.mapDomain
        (coordinateLaurentExponentDeleteAddMonoidHom a k)
        (coordinateOpenCechIntersectionLaurentRingEquiv
          (R := R) (a.delete k.succ).1 x) := by
  let q := (coordinateOpenCechIntersectionAwayIso
    (R := R) (a.delete k.succ).1).inv.hom x
  have hNat := coordinateOpenCechIntersectionAwayIso_naturality_delete
    (R := R) a k.succ
  have hNatq := ConcreteCategory.congr_hom hNat q
  change (coordinateOpenCechIntersectionAwayIso (R := R) a.1).hom.hom
      (HomogeneousLocalization.awayMap
        (homogeneousSubmodule σ R)
        (SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one R (a.1 k.succ).down)
        (coordinateProductPolynomial_eq_delete_mul (R := R) a k.succ) q) =
    ((Proj (homogeneousSubmodule σ R)).presheaf.map
      (coordinateOpenCechDelete (R := R) a k.succ).op).hom
      ((coordinateOpenCechIntersectionAwayIso
        (R := R) (a.delete k.succ).1).hom.hom q) at hNatq
  have hq : (coordinateOpenCechIntersectionAwayIso (R := R) a.1).inv.hom
      (((Proj (homogeneousSubmodule σ R)).presheaf.map
        (coordinateOpenCechDelete (R := R) a k.succ).op).hom x) =
    HomogeneousLocalization.awayMap
      (homogeneousSubmodule σ R)
      (SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one R (a.1 k.succ).down)
      (coordinateProductPolynomial_eq_delete_mul (R := R) a k.succ) q := by
    apply (coordinateOpenCechIntersectionAwayIso
      (R := R) a.1).commRingCatIsoToRingEquiv.injective
    change (coordinateOpenCechIntersectionAwayIso (R := R) a.1).hom.hom
        ((coordinateOpenCechIntersectionAwayIso (R := R) a.1).inv.hom
          (((Proj (homogeneousSubmodule σ R)).presheaf.map
            (coordinateOpenCechDelete (R := R) a k.succ).op).hom x)) =
      (coordinateOpenCechIntersectionAwayIso (R := R) a.1).hom.hom
        (HomogeneousLocalization.awayMap
          (homogeneousSubmodule σ R)
          (SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one R (a.1 k.succ).down)
          (coordinateProductPolynomial_eq_delete_mul (R := R) a k.succ) q)
    rw [Iso.inv_hom_id_apply]
    rw [show (coordinateOpenCechIntersectionAwayIso
      (R := R) (a.delete k.succ).1).hom.hom q = x by
        simpa only [q] using
          (Iso.inv_hom_id_apply
            (coordinateOpenCechIntersectionAwayIso
              (R := R) (a.delete k.succ).1) x)] at hNatq
    exact hNatq.symm
  change LaurentMonomialBasis.MvPolynomial.laurentMonomialRingEquiv R
      (StandardIntersectionRing.MvPolynomial.coordinateTailExponent (fun l => (a.1 l).down))
      (StandardIntersectionRing.MvPolynomial.coordinateProductAwayRingEquiv (R := R) (fun l => (a.1 l).down)
        ((coordinateOpenCechIntersectionAwayIso (R := R) a.1).inv.hom
          (((Proj (homogeneousSubmodule σ R)).presheaf.map
            (coordinateOpenCechDelete (R := R) a k.succ).op).hom x))) = _
  rw [hq]
  exact DFunLike.congr_fun
    (coordinateProductAwayLaurentRingEquiv_naturality_delete_succ
      (R := R) a k) q

/-- After transporting coefficients to the affine base, noninitial restriction still preserves the
underlying local Laurent exponent. -/
theorem coordinateOpenCechIntersectionBaseLaurentLinearEquiv_naturality_delete_succ
    [LinearOrder σ] {n : ℕ}
    (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (k : Fin (n + 1))
    (x : Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor
      (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      (Invertible.Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
      (coordinateOpenCover (R := R) (σ := σ)) n (a.delete k.succ).1) :
    coordinateOpenCechIntersectionBaseLaurentLinearEquiv (R := R) a.1
        ((Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf
          (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
          (Invertible.Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))).map
            (coordinateOpenCechDelete (R := R) a k.succ).op x) =
      AddMonoidAlgebra.mapDomain
        (coordinateLaurentExponentDeleteAddMonoidHom a k)
        (coordinateOpenCechIntersectionBaseLaurentLinearEquiv
          (R := R) (a.delete k.succ).1 x) := by
  let e := (Scheme.ΓSpecIso
    (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm
  let y := coordinateOpenCechIntersectionLaurentRingEquiv
    (R := R) (a.delete k.succ).1 x
  change AddMonoidAlgebra.mapRingEquiv _ e
      (coordinateOpenCechIntersectionLaurentRingEquiv (R := R) a.1
        ((Proj (homogeneousSubmodule σ R)).presheaf.map
          (coordinateOpenCechDelete (R := R) a k.succ).op x)) =
    AddMonoidAlgebra.mapDomain
      (coordinateLaurentExponentDeleteAddMonoidHom a k)
      (AddMonoidAlgebra.mapRingEquiv _ e y)
  rw [coordinateOpenCechIntersectionLaurentRingEquiv_naturality_delete_succ
    (R := R) a k x]
  exact DFunLike.congr_fun
    (AddMonoidAlgebra.mapRingHom_comp_mapDomainRingHom e.toRingHom
      (coordinateLaurentExponentDeleteAddMonoidHom a k)) y

/-- In global homogeneous-weight coordinates, a noninitial restriction is the existing deleted-
tuple inclusion. -/
theorem
    coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv_naturality_delete_succ
    [LinearOrder σ] {n : ℕ}
    (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (k : Fin (n + 1)) (d : ℤ)
    (x : Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor
      (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      (Invertible.Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
      (coordinateOpenCover (R := R) (σ := σ)) n (a.delete k.succ).1) :
    coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv
        (R := R) a.1 d
        ((Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf
          (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
          (Invertible.Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))).map
            (coordinateOpenCechDelete (R := R) a k.succ).op x) =
      coordinateHomogeneousLaurentDeleteLinearMap (R := R) a k.succ d
        (coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv
          (R := R) (a.delete k.succ).1 d x) := by
  let S := Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
  let y := coordinateOpenCechIntersectionBaseLaurentLinearEquiv
    (R := R) (a.delete k.succ).1 x
  change AddMonoidAlgebra.mapDomainLinearEquiv S S
      (LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv (fun l => (a.1 l).down) d)
      (coordinateOpenCechIntersectionBaseLaurentLinearEquiv (R := R) a.1
        ((Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf
          (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
          (Invertible.Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))).map
            (coordinateOpenCechDelete (R := R) a k.succ).op x)) =
    AddMonoidAlgebra.mapDomainLinearMap S S
      (coordinateLaurentExponentDeleteEmbedding a k.succ d)
      (AddMonoidAlgebra.mapDomainLinearEquiv S S
        (LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv
          (fun l => ((a.delete k.succ).1 l).down) d) y)
  rw [coordinateOpenCechIntersectionBaseLaurentLinearEquiv_naturality_delete_succ
    (R := R) a k x]
  change AddMonoidAlgebra.mapDomainLinearEquiv S S
      (LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv (fun l => (a.1 l).down) d)
      (AddMonoidAlgebra.mapDomain
        (coordinateLaurentExponentDeleteAddMonoidHom a k) y) = _
  induction y using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
      simp only [AddMonoidAlgebra.mapDomain_add, map_add, hx, hy]
  | single e r =>
      simp only [AddMonoidAlgebra.mapDomain_single,
        AddMonoidAlgebra.mapDomainLinearEquiv_single,
        AddMonoidAlgebra.mapDomainLinearMap_single]
      rw [coordinateLaurentExponentEquiv_delete_succ a k d e]

/-- A noninitial Cech restriction sends each homogeneous Laurent basis vector to the same global
weight in the full tuple. -/
theorem
    coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv_basis_naturality_delete_succ
    [LinearOrder σ] {n : ℕ}
    (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (k : Fin (n + 1)) (d : ℤ)
    (e : LaurentExponentLocalization.MvPolynomial.laurentExponentSubmonoid
      (StandardIntersectionRing.MvPolynomial.coordinateTailExponent (fun l => ((a.delete k.succ).1 l).down)))
    (r : Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))) :
    coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv
        (R := R) a.1 d
        ((Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf
          (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
          (Invertible.Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))).map
            (coordinateOpenCechDelete (R := R) a k.succ).op
          ((coordinateOpenCechIntersectionBaseLaurentLinearEquiv
            (R := R) (a.delete k.succ).1).symm
            (AddMonoidAlgebra.single e r))) =
      AddMonoidAlgebra.single
        (coordinateLaurentExponentDeleteEmbedding a k.succ d
          (LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv
            (fun l => ((a.delete k.succ).1 l).down) d e)) r := by
  rw [coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv_naturality_delete_succ
    (R := R) a k d]
  rw [coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv_basis_apply]
  exact coordinateHomogeneousLaurentDeleteLinearMap_single
    (R := R) a k.succ d _ r

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial
