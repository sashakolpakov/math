/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Projective.StandardCech
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OverlapTopUnit
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistPowers
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OpenFrameTransitivity
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OverFrameScalarTransfer
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OverFrameTransitions

/-! # Twist Cech Factors -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistCechFactors.MvPolynomial

noncomputable section

open _root_.MvPolynomial

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace
universe u
variable {R : Type u} {σ : Type} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The standard frame of `O(d)` restricted to an ordered Cech intersection. -/
noncomputable def coordinateHyperplaneTwistCechTrivialization {n : ℕ}
    (a : Fin (n + 1) → ULift.{u} σ) (j : σ) (d : ℤ) :
    (TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j d).restrict
        (StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := R) a).ι ≅
      Invertible.Scheme.Modules.unitObj
        (StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := R) a).toScheme :=
  OpenFrames.Scheme.Modules.restrictOpenTrivialization
    (StandardCech.MvPolynomial.coordinateOpenCechIntersection_le (R := R) a 0)
    (TwistPowers.MvPolynomial.coordinateHyperplaneTwistTrivialization (R := R) (a 0).down j d)

noncomputable def baseModulePresheafObjIsoUnitOfOverIso
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).obj (op U) ≅
      (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π (Invertible.Scheme.Modules.unitObj X)).obj (op U) := by
  let eVal := (SheafOfModules.forget (X.ringCatSheaf.over U)).mapIso e
  let eTop := (PresheafOfModules.evaluation (X.ringCatSheaf.over U).obj
    (.op (Over.mk (𝟙 U)))).mapIso eVal
  let f : Γ(S, (⊤ : S.Opens)) →+* Γ(X, U) :=
    (X.presheaf.map
      ((Limits.initialOpOfTerminal Limits.isTerminalTop).to (op U))).hom.comp
        π.appTop.hom
  exact (ModuleCat.restrictScalars f).mapIso eTop

theorem baseModulePresheafObjIsoUnitOfOverIso_naturality
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {U V : X.Opens} (hVU : V ≤ U)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).map (homOfLE hVU).op ≫
        (baseModulePresheafObjIsoUnitOfOverIso π M V
          (Dual.SheafOfModules.restrictOverTrivialization
            X.ringCatSheaf M U e (Over.mk (homOfLE hVU)))).hom =
      (baseModulePresheafObjIsoUnitOfOverIso π M U e).hom ≫
        (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π
          (Invertible.Scheme.Modules.unitObj X)).map (homOfLE hVU).op := by
  ext x
  change e.hom.val.app (.op (Over.mk (homOfLE hVU)))
      (M.presheaf.map (homOfLE hVU).op x) =
    X.presheaf.map (homOfLE hVU).op
      (e.hom.val.app (.op (Over.mk (𝟙 U))) x)
  let k : Over.mk (homOfLE hVU) ⟶ Over.mk (𝟙 U) :=
    Over.mkIdTerminal.from (Over.mk (homOfLE hVU))
  have hnat := PresheafOfModules.naturality_apply e.hom.val k.op x
  change e.hom.val.app (.op (Over.mk (homOfLE hVU)))
      ((M.over U).val.map k.op x) =
    (X.ringCatSheaf.over U).obj.map k.op
      (e.hom.val.app (.op (Over.mk (𝟙 U))) x) at hnat
  dsimp only [k] at hnat
  change e.hom.val.app (.op (Over.mk (homOfLE hVU)))
      (M.presheaf.map
        (Over.mkIdTerminal.from (Over.mk (homOfLE hVU))).left.op x) =
    X.presheaf.map
      (Over.mkIdTerminal.from (Over.mk (homOfLE hVU))).left.op
        (e.hom.val.app (.op (Over.mk (𝟙 U))) x) at hnat
  rw [Over.mkIdTerminal_from_left] at hnat
  exact hnat

noncomputable def baseModulePresheafObjUnitScalar
    {X S : Scheme.{u}} (π : X ⟶ S) (U : X.Opens) (s : Γ(X, U)) :
    (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π (Invertible.Scheme.Modules.unitObj X)).obj (op U) ⟶
      (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π (Invertible.Scheme.Modules.unitObj X)).obj (op U) := by
  let q := Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U s
  let qVal := (SheafOfModules.forget (X.ringCatSheaf.over U)).map q
  let qTop := (PresheafOfModules.evaluation (X.ringCatSheaf.over U).obj
    (.op (Over.mk (𝟙 U)))).map qVal
  let f : Γ(S, (⊤ : S.Opens)) →+* Γ(X, U) :=
    (X.presheaf.map
      ((Limits.initialOpOfTerminal Limits.isTerminalTop).to (op U))).hom.comp
        π.appTop.hom
  exact (ModuleCat.restrictScalars f).map qTop

theorem baseModulePresheafObjIsoUnitOfOverIso_comp_scalar
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules) (U : X.Opens)
    (e g : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (s : Γ(X, U))
    (h : e.hom = g.hom ≫
      Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U s) :
    (baseModulePresheafObjIsoUnitOfOverIso π M U e).hom =
      (baseModulePresheafObjIsoUnitOfOverIso π M U g).hom ≫
        baseModulePresheafObjUnitScalar π U s := by
  ext x
  change e.hom.val.app (.op (Over.mk (𝟙 U))) x =
    (Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U s).val.app
      (.op (Over.mk (𝟙 U))) (g.hom.val.app (.op (Over.mk (𝟙 U))) x)
  have happ := congrArg (fun q => q.val.app (.op (Over.mk (𝟙 U)))) h
  exact ConcreteCategory.congr_hom happ x

lemma coordinateOpenTransitionTopUnit_zpow_coe_aux
    (i k : σ) (d : ℤ) :
    ((OverlapTopUnit.MvPolynomial.coordinateOpenTransitionTopUnit (R := R) i k ^ d :
        Γ((CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k).toScheme,
          (⊤ : (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k).toScheme.Opens))ˣ) :
      Γ((CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k).toScheme,
        (⊤ : (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k).toScheme.Opens))) =
      OpenFrames.Scheme.Modules.openTopSection (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k)
        ((CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit (R := R) i k ^ d :
            Γ(Proj (homogeneousSubmodule σ R),
              CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k)ˣ) :
          Γ(Proj (homogeneousSubmodule σ R),
            CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k)) := by
  let f : Γ(Proj (homogeneousSubmodule σ R),
      CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k) →+*
      Γ((CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k).toScheme,
        (⊤ : (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k).toScheme.Opens)) :=
    (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k).topIso.inv.hom
  change (((Units.map f.toMonoidHom
      (CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit (R := R) i k)) ^ d :
        Γ((CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k).toScheme,
          (⊤ : (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k).toScheme.Opens))ˣ) :
      Γ((CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k).toScheme,
        (⊤ : (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k).toScheme.Opens))) =
    f ((CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit (R := R) i k ^ d :
      Γ(Proj (homogeneousSubmodule σ R),
        CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k)ˣ) :
      Γ(Proj (homogeneousSubmodule σ R),
        CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k))
  rw [← (Units.map f.toMonoidHom).map_zpow]
  rfl

theorem restrictOpenTrivialization_hom_eq_comp_scalar_aux
    {X : Scheme.{u}} (M : X.Modules) {U V : X.Opens} (hVU : V ≤ U)
    (e g : M.restrict U.ι ≅ Invertible.Scheme.Modules.unitObj U.toScheme)
    (r : Γ(X, U))
    (h : e.hom = g.hom ≫
      UnitScalar.unitEndomorphismOfTopSection
        (OpenFrames.Scheme.Modules.openTopSection U r)) :
    (OpenFrames.Scheme.Modules.restrictOpenTrivialization hVU e).hom =
      (OpenFrames.Scheme.Modules.restrictOpenTrivialization hVU g).hom ≫
        UnitScalar.unitEndomorphismOfTopSection
          (OpenFrames.Scheme.Modules.openTopSection V
            (X.presheaf.map (homOfLE hVU).op r)) := by
  let eOver := Invertible.Scheme.Modules.overTrivializationOfRestrictIso M U e
  let gOver := Invertible.Scheme.Modules.overTrivializationOfRestrictIso M U g
  have hOver : eOver.hom = gOver.hom ≫
      Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U r :=
    OverFrameScalarTransfer.overTrivializationOfRestrictIso_hom_eq_comp_scalar
      M U e g r h
  let eRes := Dual.SheafOfModules.restrictOverTrivialization
    X.ringCatSheaf M U eOver (Over.mk (homOfLE hVU))
  let gRes := Dual.SheafOfModules.restrictOverTrivialization
    X.ringCatSheaf M U gOver (Over.mk (homOfLE hVU))
  have hRes : eRes.hom = gRes.hom ≫
      Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf V
        (X.presheaf.map (homOfLE hVU).op r) :=
    OverFrameTransitions.restrictOverTrivialization_hom_eq_comp_scalar
      M hVU gOver eOver r hOver
  have hOpen := OverScalarRestriction.restrictTrivializationOfOverIso_hom_eq_comp_scalar
    M V eRes gRes (X.presheaf.map (homOfLE hVU).op r) hRes
  have heOver := OpenFrames.Scheme.Modules.overTrivializationOfRestrictOpenTrivialization
    hVU e
  have hgOver := OpenFrames.Scheme.Modules.overTrivializationOfRestrictOpenTrivialization
    hVU g
  have heOpen := congrArg
    (FrameSections.restrictTrivializationOfOverIso M V) heOver
  have hgOpen := congrArg
    (FrameSections.restrictTrivializationOfOverIso M V) hgOver
  rw [OpenFrames.restrictTrivializationOfOverTrivializationOfRestrictIso]
    at heOpen hgOpen
  rw [← heOpen, ← hgOpen] at hOpen
  exact hOpen

/-- A twist Cech factor is the corresponding structure-sheaf section module. -/
noncomputable def coordinateHyperplaneTwistBaseCechFactorIsoUnit {n : ℕ}
    (a : Fin (n + 1) → ULift.{u} σ) (j : σ) (d : ℤ) :
    Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor
        (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j d)
        (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) n a ≅
      Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor
        (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (Invertible.Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
        (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) n a :=
  baseModulePresheafObjIsoUnitOfOverIso
    (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
    (TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j d)
    (StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := R) a)
    (Invertible.Scheme.Modules.overTrivializationOfRestrictIso
      (TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j d)
      (StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := R) a)
      (coordinateHyperplaneTwistCechTrivialization (R := R) a j d))

/-- The order relation underlying `coordinateOpenCechDelete`. -/
theorem coordinateOpenCechDelete_le [LinearOrder σ] {n : ℕ}
    (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (k : Fin (n + 2)) :
    StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := R) a.1 ≤
      StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := R) (a.delete k).1 :=
  leOfHom (StandardCech.MvPolynomial.coordinateOpenCechDelete (R := R) a k)

/-- A full ordered Cech intersection lies in the overlap of its first two
standard charts. -/
theorem coordinateOpenCechIntersection_le_firstOverlap [LinearOrder σ] {n : ℕ}
    (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) :
    StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := R) a.1 ≤
      CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) (a.1 0).down (a.1 1).down := by
  rw [CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_eq]
  exact le_inf
    (StandardCech.MvPolynomial.coordinateOpenCechIntersection_le (R := R) a.1 0)
    (StandardCech.MvPolynomial.coordinateOpenCechIntersection_le (R := R) a.1 1)

/-- The first-chart transition section is the Laurent monomial represented by the second
coordinate divided by the first. -/
theorem coordinateOpenCechFirstTransition_laurent [LinearOrder σ] {n : ℕ}
    (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) :
    let h10 : (a.1 1).down ≠ (a.1 0).down := by
      intro h
      have ha : a.1 1 = a.1 0 := ULift.ext _ _ h
      exact one_ne_zero (a.2.injective ha)
    StandardCech.MvPolynomial.coordinateOpenCechIntersectionLaurentRingEquiv (R := R) a.1
        ((Proj (homogeneousSubmodule σ R)).presheaf.map
          (homOfLE (coordinateOpenCechIntersection_le_firstOverlap
            (R := R) a)).op
          (CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit
            (R := R) (a.1 0).down (a.1 1).down :
            Γ(Proj (homogeneousSubmodule σ R),
              CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) (a.1 0).down (a.1 1).down))) =
      AddMonoidAlgebra.single
        (LaurentExponentLocalization.MvPolynomial.laurentExponentAwayMap
          (StandardIntersectionRing.MvPolynomial.coordinateTailExponent (fun k => (a.1 k).down))
          (Finsupp.single ⟨(a.1 1).down, h10⟩ 1)) 1 := by
  dsimp only
  let h10 : (a.1 1).down ≠ (a.1 0).down := by
    intro h
    have ha : a.1 1 = a.1 0 := ULift.ext _ _ h
    exact one_ne_zero (a.2.injective ha)
  let q : HomogeneousLocalization.Away
      (homogeneousSubmodule σ R) (X (a.1 0).down) :=
    SpaceChart.MvPolynomial.awayVar R (a.1 0).down ⟨(a.1 1).down, h10⟩
  have hsection :
      (Proj (homogeneousSubmodule σ R)).presheaf.map
          (homOfLE (coordinateOpenCechIntersection_le_firstOverlap
            (R := R) a)).op
          (CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit
            (R := R) (a.1 0).down (a.1 1).down :
            Γ(Proj (homogeneousSubmodule σ R),
              CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) (a.1 0).down (a.1 1).down)) =
        (Proj (homogeneousSubmodule σ R)).presheaf.map
          (homOfLE (StandardCech.MvPolynomial.coordinateOpenCechIntersection_le (R := R) a.1 0)).op
          ((Proj.basicOpenIsoAway (homogeneousSubmodule σ R) (X (a.1 0).down)
            (SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one R (a.1 0).down) one_pos).hom.hom q) := by
    change (Proj (homogeneousSubmodule σ R)).presheaf.map
        (homOfLE (coordinateOpenCechIntersection_le_firstOverlap
          (R := R) a)).op
        ((Proj (homogeneousSubmodule σ R)).presheaf.map
          (homOfLE (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left
            (R := R) (a.1 0).down (a.1 1).down)).op
          (CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation
            (R := R) (a.1 0).down (a.1 1).down)) = _
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rw [show (homOfLE (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left
        (R := R) (a.1 0).down (a.1 1).down)).op ≫
          (homOfLE (coordinateOpenCechIntersection_le_firstOverlap
            (R := R) a)).op =
        (homOfLE (StandardCech.MvPolynomial.coordinateOpenCechIntersection_le (R := R) a.1 0)).op
      from Subsingleton.elim _ _]
    rw [CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation_of_ne
      (R := R) (a.1 0).down (a.1 1).down h10]
  rw [hsection]
  let qFull := HomogeneousLocalization.awayMap
    (f := X (a.1 0).down)
    (g := StandardIntersectionRing.MvPolynomial.coordinateTailPolynomial (R := R) (fun k => (a.1 k).down))
    (x := StandardIntersectionRing.MvPolynomial.coordinateProductPolynomial (R := R) (fun k => (a.1 k).down))
    (homogeneousSubmodule σ R)
    (StandardIntersectionRing.MvPolynomial.coordinateTailPolynomial_mem (R := R) (fun k => (a.1 k).down))
    (show StandardIntersectionRing.MvPolynomial.coordinateProductPolynomial (R := R) (fun k => (a.1 k).down) =
      X (a.1 0).down * StandardIntersectionRing.MvPolynomial.coordinateTailPolynomial (R := R) (fun k => (a.1 k).down)
      by rw [StandardIntersectionRing.MvPolynomial.coordinateProductPolynomial]) q
  have hNat := StandardCech.MvPolynomial.coordinateOpenCechIntersectionAwayIso_naturality_firstChart
    (R := R) a.1
  have hNatq := ConcreteCategory.congr_hom hNat q
  simp only [ConcreteCategory.comp_apply] at hNatq
  have hq' := congrArg
    (fun z => (StandardCech.MvPolynomial.coordinateOpenCechIntersectionAwayIso (R := R) a.1).inv.hom z)
    hNatq
  rw [Iso.hom_inv_id_apply] at hq'
  have hq : (StandardCech.MvPolynomial.coordinateOpenCechIntersectionAwayIso (R := R) a.1).inv.hom
      ((Proj (homogeneousSubmodule σ R)).presheaf.map
        (homOfLE (StandardCech.MvPolynomial.coordinateOpenCechIntersection_le (R := R) a.1 0)).op
        ((Proj.basicOpenIsoAway (homogeneousSubmodule σ R) (X (a.1 0).down)
          (SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one R (a.1 0).down) one_pos).hom.hom q)) =
      qFull := by
    exact hq'.symm
  change LaurentMonomialBasis.MvPolynomial.laurentMonomialRingEquiv R _
      (StandardIntersectionRing.MvPolynomial.coordinateProductAwayRingEquiv (R := R) _
        ((StandardCech.MvPolynomial.coordinateOpenCechIntersectionAwayIso (R := R) a.1).inv.hom _)) = _
  rw [hq]
  rw [StandardIntersectionRing.MvPolynomial.coordinateProductAwayLaurentRingEquiv_awayMap]
  rw [SpaceChart.MvPolynomial.chartRingEquiv_apply_awayVar]
  change AddMonoidAlgebra.mapDomain _
      (AddMonoidAlgebra.single
        (Finsupp.single
          (⟨(a.1 1).down, h10⟩ : {j : σ // j ≠ (a.1 0).down}) 1) 1) = _
  rw [AddMonoidAlgebra.mapDomain_single]
  rfl

/-- The first two entries of an ordered Cech index are distinct. -/
theorem coordinateOpenCechFirstSecond_ne [LinearOrder σ] {n : ℕ}
    (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) :
    (a.1 1).down ≠ (a.1 0).down := by
  intro h
  have ha : a.1 1 = a.1 0 := ULift.ext _ _ h
  exact one_ne_zero (a.2.injective ha)

/-- The local Laurent exponent of an integer power of the first transition unit. -/
noncomputable def coordinateOpenCechFirstTransitionExponent [LinearOrder σ] {n : ℕ}
    (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) :
    ℤ →+ LaurentExponentLocalization.MvPolynomial.laurentExponentSubmonoid
      (StandardIntersectionRing.MvPolynomial.coordinateTailExponent (fun k => (a.1 k).down)) where
  toFun d := ⟨Finsupp.single
    (⟨(a.1 1).down, coordinateOpenCechFirstSecond_ne a⟩ :
      {j : σ // j ≠ (a.1 0).down}) d, by
    intro i hi
    by_cases hij : i =
        (⟨(a.1 1).down, coordinateOpenCechFirstSecond_ne a⟩ :
          {j : σ // j ≠ (a.1 0).down})
    · subst i
      exact (StandardIntersectionRing.MvPolynomial.coordinateTailExponent_ne_zero_iff
        (fun k => (a.1 k).down)
        (⟨(a.1 1).down, coordinateOpenCechFirstSecond_ne a⟩ :
          {j : σ // j ≠ (a.1 0).down})).2 ⟨1, rfl⟩
    · simp [hij] at hi⟩
  map_zero' := by
    apply Subtype.ext
    simp
  map_add' d e := by
    apply Subtype.ext
    simp

noncomputable def coordinateOpenCechFirstTransitionLaurentUnit
    [LinearOrder σ] {n : ℕ}
    (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) :
    (AddMonoidAlgebra R
      (LaurentExponentLocalization.MvPolynomial.laurentExponentSubmonoid
        (StandardIntersectionRing.MvPolynomial.coordinateTailExponent (fun k => (a.1 k).down))))ˣ where
  val := AddMonoidAlgebra.single
    (coordinateOpenCechFirstTransitionExponent (n := n) a 1) 1
  inv := AddMonoidAlgebra.single
    (coordinateOpenCechFirstTransitionExponent (n := n) a (-1)) 1
  val_inv := by
    rw [AddMonoidAlgebra.single_mul_single, ← map_add]
    norm_num
    exact AddMonoidAlgebra.one_def.symm
  inv_val := by
    rw [AddMonoidAlgebra.single_mul_single, ← map_add]
    norm_num
    exact AddMonoidAlgebra.one_def.symm

lemma coordinateOpenCechFirstTransitionLaurentUnit_zpow_val
    [LinearOrder σ] {n : ℕ}
    (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) (d : ℤ) :
    ((coordinateOpenCechFirstTransitionLaurentUnit (R := R) (n := n) a ^ d :
        (AddMonoidAlgebra R
          (LaurentExponentLocalization.MvPolynomial.laurentExponentSubmonoid
            (StandardIntersectionRing.MvPolynomial.coordinateTailExponent (fun k => (a.1 k).down))))ˣ) :
      AddMonoidAlgebra R
        (LaurentExponentLocalization.MvPolynomial.laurentExponentSubmonoid
          (StandardIntersectionRing.MvPolynomial.coordinateTailExponent (fun k => (a.1 k).down)))) =
      AddMonoidAlgebra.single
        (coordinateOpenCechFirstTransitionExponent (n := n) a d) 1 := by
  cases d with
  | ofNat m =>
      calc
        _ = (↑((coordinateOpenCechFirstTransitionLaurentUnit
            (R := R) (n := n) a) ^ m) :
            AddMonoidAlgebra R
              (LaurentExponentLocalization.MvPolynomial.laurentExponentSubmonoid
                (StandardIntersectionRing.MvPolynomial.coordinateTailExponent (fun k => (a.1 k).down)))) :=
          congrArg Units.val
            (zpow_natCast
              (coordinateOpenCechFirstTransitionLaurentUnit
                (R := R) (n := n) a) m)
        _ = _ := by
          rw [Units.val_pow_eq_pow_val]
          change (AddMonoidAlgebra.single
            (coordinateOpenCechFirstTransitionExponent (n := n) a 1) 1) ^ m = _
          rw [AddMonoidAlgebra.single_pow, one_pow, ← map_nsmul]
          congr
          simp
  | negSucc m =>
      rw [zpow_negSucc, ← inv_pow, Units.val_pow_eq_pow_val]
      change (AddMonoidAlgebra.single
        (coordinateOpenCechFirstTransitionExponent (n := n) a (-1)) 1) ^ (m + 1) = _
      rw [AddMonoidAlgebra.single_pow, one_pow, ← map_nsmul]
      congr
      simp [Int.negSucc_eq]

/-- The Laurent image of an integer power of the first transition unit is the corresponding
single Laurent monomial. -/
theorem coordinateOpenCechFirstTransition_zpow_laurent
    [LinearOrder σ] {n : ℕ}
    (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) (d : ℤ) :
    StandardCech.MvPolynomial.coordinateOpenCechIntersectionLaurentRingEquiv (R := R) a.1
        ((Proj (homogeneousSubmodule σ R)).presheaf.map
          (homOfLE (coordinateOpenCechIntersection_le_firstOverlap
            (R := R) a)).op
          ((CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit
              (R := R) (a.1 0).down (a.1 1).down ^ d :
            Γ(Proj (homogeneousSubmodule σ R),
              CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) (a.1 0).down (a.1 1).down)ˣ) :
            Γ(Proj (homogeneousSubmodule σ R),
              CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) (a.1 0).down (a.1 1).down))) =
      AddMonoidAlgebra.single
        (coordinateOpenCechFirstTransitionExponent (n := n) a d) 1 := by
  let f := (StandardCech.MvPolynomial.coordinateOpenCechIntersectionLaurentRingEquiv
      (R := R) a.1).toRingHom.comp
    ((Proj (homogeneousSubmodule σ R)).presheaf.map
      (homOfLE (coordinateOpenCechIntersection_le_firstOverlap
        (R := R) a)).op).hom
  let t := CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit
    (R := R) (a.1 0).down (a.1 1).down
  have ht : Units.map f.toMonoidHom t =
      coordinateOpenCechFirstTransitionLaurentUnit (R := R) (n := n) a := by
    apply Units.ext
    change StandardCech.MvPolynomial.coordinateOpenCechIntersectionLaurentRingEquiv (R := R) a.1
        ((Proj (homogeneousSubmodule σ R)).presheaf.map
          (homOfLE (coordinateOpenCechIntersection_le_firstOverlap
            (R := R) a)).op
          (CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit
            (R := R) (a.1 0).down (a.1 1).down :
            Γ(Proj (homogeneousSubmodule σ R),
              CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) (a.1 0).down (a.1 1).down))) = _
    rw [coordinateOpenCechFirstTransition_laurent]
    apply congrArg (fun e => AddMonoidAlgebra.single e (1 : R))
    apply Subtype.ext
    ext i
    rw [LaurentExponentLocalization.MvPolynomial.laurentExponentAwayMap_apply]
    let j : {j : σ // j ≠ (a.1 0).down} :=
      ⟨(a.1 1).down, coordinateOpenCechFirstSecond_ne (n := n) a⟩
    change ((Finsupp.single j 1 i : ℕ) : ℤ) = Finsupp.single j 1 i
    by_cases hi : i = j
    · subst i
      simp
    · simp [hi]
  change f ((t ^ d :
    Γ(Proj (homogeneousSubmodule σ R),
      CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) (a.1 0).down (a.1 1).down)ˣ) : _) = _
  calc
    _ = (↑(Units.map f.toMonoidHom (t ^ d)) :
        AddMonoidAlgebra R
          (LaurentExponentLocalization.MvPolynomial.laurentExponentSubmonoid
            (StandardIntersectionRing.MvPolynomial.coordinateTailExponent (fun k => (a.1 k).down)))) :=
      (Units.coe_map f.toMonoidHom (t ^ d)).symm
    _ = (↑((Units.map f.toMonoidHom t) ^ d) :
        AddMonoidAlgebra R
          (LaurentExponentLocalization.MvPolynomial.laurentExponentSubmonoid
            (StandardIntersectionRing.MvPolynomial.coordinateTailExponent (fun k => (a.1 k).down)))) := by
      exact congrArg Units.val ((Units.map f.toMonoidHom).map_zpow t d)
    _ = _ := by
      simpa only [ht] using
        (coordinateOpenCechFirstTransitionLaurentUnit_zpow_val
          (R := R) (n := n) a d)

noncomputable def coordinateLaurentExponentDeleteZeroRaw
    [LinearOrder σ] {n : ℕ}
    (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (e : LaurentExponentLocalization.MvPolynomial.laurentExponentSubmonoid
      (StandardIntersectionRing.MvPolynomial.coordinateTailExponent (fun k => ((a.delete 0).1 k).down))) :
    LaurentExponentLocalization.MvPolynomial.laurentExponentSubmonoid
      (StandardIntersectionRing.MvPolynomial.coordinateTailExponent (fun k => (a.1 k).down)) :=
  (LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv (fun k => (a.1 k).down) 0).symm
    (StandardCech.MvPolynomial.coordinateLaurentExponentDeleteEmbedding a 0 0
      (LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv
        (fun k => ((a.delete 0).1 k).down) 0 e))

lemma coordinateLaurentExponentDeleteZeroRaw_apply
    [LinearOrder σ] {n : ℕ}
    (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (e : LaurentExponentLocalization.MvPolynomial.laurentExponentSubmonoid
      (StandardIntersectionRing.MvPolynomial.coordinateTailExponent (fun k => ((a.delete 0).1 k).down)))
    (j : {j : σ // j ≠ (a.1 0).down}) :
    (coordinateLaurentExponentDeleteZeroRaw a e).1 j =
      (LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv
        (fun k => ((a.delete 0).1 k).down) 0 e).1.1 j.1 := by
  rw [coordinateLaurentExponentDeleteZeroRaw,
    LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv_symm_apply]
  rfl

theorem coordinateLaurentExponentEquiv_zero_apply_zero
    {n : ℕ} (b : Fin (n + 1) → σ) (i : σ) :
    (LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv b 0
      (0 : LaurentExponentLocalization.MvPolynomial.laurentExponentSubmonoid (StandardIntersectionRing.MvPolynomial.coordinateTailExponent b))).1.1 i = 0 := by
  by_cases hi : i = b 0
  · subst i
    rw [LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv_apply_anchor]
    simp
  · rw [LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv_apply_of_ne _ _ _ _ hi]
    rfl

theorem coordinateLaurentExponentEquiv_zero_apply_add
    {n : ℕ} (b : Fin (n + 1) → σ)
    (e f : LaurentExponentLocalization.MvPolynomial.laurentExponentSubmonoid (StandardIntersectionRing.MvPolynomial.coordinateTailExponent b)) (i : σ) :
    (LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv b 0 (e + f)).1.1 i =
      (LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv b 0 e).1.1 i +
        (LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv b 0 f).1.1 i := by
  by_cases hi : i = b 0
  · subst i
    rw [LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv_apply_anchor,
      LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv_apply_anchor,
      LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv_apply_anchor]
    change 0 - Finsupp.degree (e.1 + f.1) =
      (0 - Finsupp.degree e.1) + (0 - Finsupp.degree f.1)
    rw [map_add]
    omega
  · rw [LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv_apply_of_ne _ _ _ _ hi,
      LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv_apply_of_ne _ _ _ _ hi,
      LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv_apply_of_ne _ _ _ _ hi]
    rfl

/-- Restricting from the chart anchored at the second coordinate to the full intersection, expressed
in Laurent exponents for the chart anchored at the first coordinate. -/
noncomputable def coordinateLaurentExponentDeleteZeroAddMonoidHom
    [LinearOrder σ] {n : ℕ}
    (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) :
    LaurentExponentLocalization.MvPolynomial.laurentExponentSubmonoid
        (StandardIntersectionRing.MvPolynomial.coordinateTailExponent (fun k => ((a.delete 0).1 k).down)) →+
      LaurentExponentLocalization.MvPolynomial.laurentExponentSubmonoid
        (StandardIntersectionRing.MvPolynomial.coordinateTailExponent (fun k => (a.1 k).down)) where
  toFun := coordinateLaurentExponentDeleteZeroRaw a
  map_zero' := by
    apply Subtype.ext
    ext j
    rw [coordinateLaurentExponentDeleteZeroRaw_apply]
    exact coordinateLaurentExponentEquiv_zero_apply_zero
      (fun k => ((a.delete 0).1 k).down) j.1
  map_add' e f := by
    apply Subtype.ext
    ext j
    change (coordinateLaurentExponentDeleteZeroRaw a (e + f)).1 j =
      (coordinateLaurentExponentDeleteZeroRaw a e).1 j +
        (coordinateLaurentExponentDeleteZeroRaw a f).1 j
    rw [coordinateLaurentExponentDeleteZeroRaw_apply,
      coordinateLaurentExponentDeleteZeroRaw_apply,
      coordinateLaurentExponentDeleteZeroRaw_apply]
    exact coordinateLaurentExponentEquiv_zero_apply_add
      (fun k => ((a.delete 0).1 k).down) e f j.1

/-- The first-deletion exponent map reads the same degree-zero global homogeneous exponent in the
new anchor chart. -/
@[simp]
theorem coordinateLaurentExponentDeleteZeroAddMonoidHom_apply
    [LinearOrder σ] {n : ℕ}
    (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (e : LaurentExponentLocalization.MvPolynomial.laurentExponentSubmonoid
      (StandardIntersectionRing.MvPolynomial.coordinateTailExponent (fun k => ((a.delete 0).1 k).down)))
    (j : {j : σ // j ≠ (a.1 0).down}) :
    (coordinateLaurentExponentDeleteZeroAddMonoidHom a e).1 j =
      (LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv
        (fun k => ((a.delete 0).1 k).down) 0 e).1.1 j.1 :=
  coordinateLaurentExponentDeleteZeroRaw_apply a e j

@[simp]
theorem coordinateOpenCechFirstTransitionExponent_apply_second
    [LinearOrder σ] {n : ℕ}
    (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) (d : ℤ) :
    (coordinateOpenCechFirstTransitionExponent (n := n) a d).1
        ⟨(a.1 1).down, coordinateOpenCechFirstSecond_ne (n := n) a⟩ = d := by
  simp [coordinateOpenCechFirstTransitionExponent]

theorem coordinateOpenCechFirstTransitionExponent_apply_of_ne
    [LinearOrder σ] {n : ℕ}
    (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) (d : ℤ)
    (j : {j : σ // j ≠ (a.1 0).down}) (hj : j.1 ≠ (a.1 1).down) :
    (coordinateOpenCechFirstTransitionExponent (n := n) a d).1 j = 0 := by
  have hj' :
      (⟨(a.1 1).down, coordinateOpenCechFirstSecond_ne (n := n) a⟩ :
        {j : σ // j ≠ (a.1 0).down}) ≠ j := by
    intro h
    exact hj (congrArg Subtype.val h).symm
  simp [coordinateOpenCechFirstTransitionExponent, hj']

@[simp]
theorem coordinateOpenCechFirstTransitionExponent_degree
    [LinearOrder σ] {n : ℕ}
    (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) (d : ℤ) :
    Finsupp.degree (coordinateOpenCechFirstTransitionExponent (n := n) a d).1 = d := by
  simp [coordinateOpenCechFirstTransitionExponent, Finsupp.degree_single]

theorem coordinateLaurentExponentDeleteZeroAddMonoidHom_degree
    [LinearOrder σ] {n : ℕ}
    (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (e : LaurentExponentLocalization.MvPolynomial.laurentExponentSubmonoid
      (StandardIntersectionRing.MvPolynomial.coordinateTailExponent (fun k => ((a.delete 0).1 k).down))) :
    Finsupp.degree (coordinateLaurentExponentDeleteZeroAddMonoidHom a e).1 =
      - (LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv
        (fun k => ((a.delete 0).1 k).down) 0 e).1.1 (a.1 0).down := by
  have h := (LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv
    (fun k => (a.1 k).down) 0).apply_symm_apply
      (StandardCech.MvPolynomial.coordinateLaurentExponentDeleteEmbedding a 0 0
        (LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv
          (fun k => ((a.delete 0).1 k).down) 0 e))
  have h0 := congrArg
    (fun z => z.1.1 (a.1 0).down) h
  change (LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv
      (fun k => (a.1 k).down) 0
      (coordinateLaurentExponentDeleteZeroAddMonoidHom a e)).1.1 (a.1 0).down =
    (LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv
      (fun k => ((a.delete 0).1 k).down) 0 e).1.1 (a.1 0).down at h0
  rw [LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv_apply_anchor] at h0
  omega

/-- First-deletion restriction followed by the twist transition gives the same global homogeneous
exponent as inclusion from the deleted tuple. -/
theorem coordinateLaurentExponentEquiv_delete_zero_add_transition
    [LinearOrder σ] {n : ℕ}
    (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) (d : ℤ)
    (e : LaurentExponentLocalization.MvPolynomial.laurentExponentSubmonoid
      (StandardIntersectionRing.MvPolynomial.coordinateTailExponent (fun k => ((a.delete 0).1 k).down))) :
    LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv (fun k => (a.1 k).down) d
        (coordinateLaurentExponentDeleteZeroAddMonoidHom a e +
          coordinateOpenCechFirstTransitionExponent (n := n) a d) =
      StandardCech.MvPolynomial.coordinateLaurentExponentDeleteEmbedding a 0 d
        (LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv
          (fun k => ((a.delete 0).1 k).down) d e) := by
  apply Subtype.ext
  apply Subtype.ext
  ext i
  change (LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv (fun k => (a.1 k).down) d
      (coordinateLaurentExponentDeleteZeroAddMonoidHom a e +
        coordinateOpenCechFirstTransitionExponent (n := n) a d)).1.1 i =
    (LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv
      (fun k => ((a.delete 0).1 k).down) d e).1.1 i
  by_cases hi0 : i = (a.1 0).down
  · subst i
    rw [LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv_apply_anchor]
    change d - Finsupp.degree
        ((coordinateLaurentExponentDeleteZeroAddMonoidHom a e).1 +
          (coordinateOpenCechFirstTransitionExponent (n := n) a d).1) = _
    rw [map_add,
      coordinateLaurentExponentDeleteZeroAddMonoidHom_degree,
      coordinateOpenCechFirstTransitionExponent_degree]
    have h01 : (a.1 0).down ≠ ((a.delete 0).1 0).down := by
      exact (coordinateOpenCechFirstSecond_ne (n := n) a).symm
    rw [LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv_apply_of_ne _ _ _ _ h01,
      LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv_apply_of_ne _ _ _ _ h01]
    omega
  · rw [LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv_apply_of_ne _ _ _ _ hi0]
    change (coordinateLaurentExponentDeleteZeroAddMonoidHom a e).1 ⟨i, hi0⟩ +
        (coordinateOpenCechFirstTransitionExponent (n := n) a d).1 ⟨i, hi0⟩ = _
    rw [coordinateLaurentExponentDeleteZeroAddMonoidHom_apply]
    by_cases hi1 : i = (a.1 1).down
    · subst i
      rw [coordinateOpenCechFirstTransitionExponent_apply_second]
      change (LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv
          (fun k => ((a.delete 0).1 k).down) 0 e).1.1
            ((a.delete 0).1 0).down + d = _
      have hanchor : ((a.delete 0).1 0).down = (a.1 1).down := rfl
      rw [← hanchor, LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv_apply_anchor,
        LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv_apply_anchor]
      omega
    · rw [coordinateOpenCechFirstTransitionExponent_apply_of_ne
        (a := a) d ⟨i, hi0⟩ hi1, add_zero]
      have hi1' : i ≠ ((a.delete 0).1 0).down := hi1
      rw [LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv_apply_of_ne _ _ _ _ hi1',
        LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv_apply_of_ne _ _ _ _ hi1']

noncomputable def coordinateOpenCechFirstTransitionRingHom
    [LinearOrder σ] {n : ℕ}
    (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) :
    Γ(Proj (homogeneousSubmodule σ R),
        CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) (a.1 0).down (a.1 1).down) →+*
      Γ((StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := R) a.1).toScheme,
        (⊤ : (StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := R) a.1).toScheme.Opens)) :=
  (StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := R) a.1).topIso.inv.hom.comp
    ((Proj (homogeneousSubmodule σ R)).presheaf.map
      (homOfLE (coordinateOpenCechIntersection_le_firstOverlap
        (R := R) a)).op).hom

/-- The first-chart transition unit, restricted to a full ordered Cech
intersection and transported to its top ring. -/
noncomputable def coordinateOpenCechFirstTransitionTopUnit
    [LinearOrder σ] {n : ℕ}
    (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) :
    Γ((StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := R) a.1).toScheme,
      (⊤ : (StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := R) a.1).toScheme.Opens))ˣ :=
  Units.map (coordinateOpenCechFirstTransitionRingHom (R := R) a).toMonoidHom
    (CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit (R := R) (a.1 0).down (a.1 1).down)

lemma coordinateOpenCechFirstTransitionTopUnit_zpow_coe
    [LinearOrder σ] {n : ℕ}
    (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) (d : ℤ) :
    ((coordinateOpenCechFirstTransitionTopUnit (R := R) a ^ d :
        Γ((StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := R) a.1).toScheme,
          (⊤ : (StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := R) a.1).toScheme.Opens))ˣ) :
      Γ((StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := R) a.1).toScheme,
        (⊤ : (StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := R) a.1).toScheme.Opens))) =
      OpenFrames.Scheme.Modules.openTopSection (StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := R) a.1)
        ((Proj (homogeneousSubmodule σ R)).presheaf.map
          (homOfLE (coordinateOpenCechIntersection_le_firstOverlap
            (R := R) a)).op
          ((CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit (R := R) (a.1 0).down (a.1 1).down ^ d :
              Γ(Proj (homogeneousSubmodule σ R),
                CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) (a.1 0).down (a.1 1).down)ˣ) :
            Γ(Proj (homogeneousSubmodule σ R),
              CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) (a.1 0).down (a.1 1).down))) := by
  let f := coordinateOpenCechFirstTransitionRingHom (R := R) a
  change (((Units.map f.toMonoidHom
      (CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit (R := R) (a.1 0).down (a.1 1).down)) ^ d :
        Γ((StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := R) a.1).toScheme,
          (⊤ : (StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := R) a.1).toScheme.Opens))ˣ) :
      Γ((StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := R) a.1).toScheme,
        (⊤ : (StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := R) a.1).toScheme.Opens))) =
    f ((CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit (R := R) (a.1 0).down (a.1 1).down ^ d :
      Γ(Proj (homogeneousSubmodule σ R),
        CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) (a.1 0).down (a.1 1).down)ˣ) :
      Γ(Proj (homogeneousSubmodule σ R),
        CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) (a.1 0).down (a.1 1).down))
  rw [← (Units.map f.toMonoidHom).map_zpow]
  rfl

/-- Multiplication by the first-chart transition unit on the structure-sheaf
factor of a full ordered Cech intersection. -/
noncomputable def coordinateOpenCechFirstTransitionFactorEnd
    [LinearOrder σ] {n : ℕ}
    (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) (d : ℤ) :
    Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor
        (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (Invertible.Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
        (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) (n + 1) a.1 ⟶
      Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor
        (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (Invertible.Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
        (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) (n + 1) a.1 :=
  baseModulePresheafObjUnitScalar
    (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
    (StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := R) a.1)
    ((Proj (homogeneousSubmodule σ R)).presheaf.map
      (homOfLE (coordinateOpenCechIntersection_le_firstOverlap
        (R := R) a)).op
      ((CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit (R := R) (a.1 0).down (a.1 1).down ^ d :
          Γ(Proj (homogeneousSubmodule σ R),
            CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) (a.1 0).down (a.1 1).down)ˣ) :
          Γ(Proj (homogeneousSubmodule σ R),
            CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) (a.1 0).down (a.1 1).down)))

/-- In Laurent coordinates, the first-chart transition endomorphism is multiplication by the
restricted transition section. -/
theorem coordinateOpenCechFirstTransitionFactorEnd_apply_laurent
    [LinearOrder σ] {n : ℕ}
    (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) (d : ℤ)
    (x : Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor
      (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      (Invertible.Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
      (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) (n + 1) a.1) :
    StandardCech.MvPolynomial.coordinateOpenCechIntersectionBaseLaurentLinearEquiv (R := R) a.1
        (coordinateOpenCechFirstTransitionFactorEnd (R := R) a d x) =
      StandardCech.MvPolynomial.coordinateOpenCechIntersectionBaseLaurentLinearEquiv (R := R) a.1 x *
        StandardCech.MvPolynomial.coordinateOpenCechIntersectionBaseLaurentRingEquiv (R := R) a.1
          ((Proj (homogeneousSubmodule σ R)).presheaf.map
            (homOfLE (coordinateOpenCechIntersection_le_firstOverlap
              (R := R) a)).op
            ((CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit
                (R := R) (a.1 0).down (a.1 1).down ^ d :
              Γ(Proj (homogeneousSubmodule σ R),
                CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) (a.1 0).down (a.1 1).down)ˣ) :
              Γ(Proj (homogeneousSubmodule σ R),
                CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) (a.1 0).down (a.1 1).down))) := by
  let X := Proj (homogeneousSubmodule σ R)
  let U := StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := R) a.1
  let s : Γ(X, U) := X.presheaf.map
    (homOfLE (coordinateOpenCechIntersection_le_firstOverlap (R := R) a)).op
    ((CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit
        (R := R) (a.1 0).down (a.1 1).down ^ d :
      Γ(X, CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) (a.1 0).down (a.1 1).down)ˣ) :
      Γ(X, CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) (a.1 0).down (a.1 1).down))
  change StandardCech.MvPolynomial.coordinateOpenCechIntersectionBaseLaurentRingEquiv (R := R) a.1
      ((Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U s).val.app
        (.op (Over.mk (𝟙 U))) x) = _
  change StandardCech.MvPolynomial.coordinateOpenCechIntersectionBaseLaurentRingEquiv (R := R) a.1
      ((show Γ(X, U) from x) * s) = _
  rw [map_mul]
  rfl

/-- Deleting a noninitial entry preserves the anchor frame on the smaller
standard intersection. -/
theorem coordinateHyperplaneTwistCechTrivialization_restrict_delete_of_ne_zero
    [LinearOrder σ] {n : ℕ}
    (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (k : Fin (n + 2)) (hk : k ≠ 0) (j : σ) (d : ℤ) :
    OpenFrames.Scheme.Modules.restrictOpenTrivialization
        (coordinateOpenCechDelete_le (R := R) a k)
        (coordinateHyperplaneTwistCechTrivialization
          (R := R) (a.delete k).1 j d) =
      coordinateHyperplaneTwistCechTrivialization (R := R) a.1 j d := by
  obtain ⟨k, rfl⟩ := Fin.eq_succ_of_ne_zero hk
  rw [coordinateHyperplaneTwistCechTrivialization,
    OpenFrameTransitivity.Scheme.Modules.restrictOpenTrivialization_comp]
  rfl

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistCechFactors.MvPolynomial
