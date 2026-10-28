/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Projective.HyperplaneIdeal

/-! # Coordinate Extensions -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial

noncomputable section

open _root_.MvPolynomial

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.HomogeneousIdeal
universe u
variable {R : Type u} {σ : Type} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The local equation of the coordinate hyperplane `X j = 0` on the standard
chart `D₊(X i)`: it is `1` on the `j`-chart and `X j / X i` otherwise. -/
noncomputable def coordinateHyperplaneLocalEquation (i j : σ) :
    Γ(Proj (homogeneousSubmodule σ R), MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) := by
  classical
  exact if hji : j = i then 1 else
      (Proj.basicOpenIsoAway (homogeneousSubmodule σ R) (X i)
        (SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one R i) one_pos).hom.hom
          (SpaceChart.MvPolynomial.awayVar R i ⟨j, hji⟩)

@[simp]
lemma coordinateHyperplaneLocalEquation_self (j : σ) :
    coordinateHyperplaneLocalEquation (R := R) j j = 1 := by
  simp [coordinateHyperplaneLocalEquation]

lemma coordinateHyperplaneLocalEquation_of_ne (i j : σ) (hji : j ≠ i) :
    coordinateHyperplaneLocalEquation (R := R) i j =
      (Proj.basicOpenIsoAway (homogeneousSubmodule σ R) (X i)
        (SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one R i) one_pos).hom.hom
          (SpaceChart.MvPolynomial.awayVar R i ⟨j, hji⟩) := by
  simp [coordinateHyperplaneLocalEquation, hji]

/-- The homogeneous-localization element defining the preimage of `D₊(X j)` on the
`X i`-chart maps to the local equation of the coordinate hyperplane. -/
lemma coordinateHyperplaneLocalEquation_eq_isLocalizationElem (i j : σ) :
    coordinateHyperplaneLocalEquation (R := R) i j =
      (Proj.basicOpenIsoAway (homogeneousSubmodule σ R) (X i)
        (SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one R i) one_pos).hom.hom
          (HomogeneousLocalization.Away.isLocalizationElem
            (SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one R i)
            (SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one R j)) := by
  classical
  by_cases hji : j = i
  · subst j
    rw [coordinateHyperplaneLocalEquation_self]
    have hloc :
        HomogeneousLocalization.Away.isLocalizationElem
            (SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one R i)
            (SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one R i) = 1 := by
      apply HomogeneousLocalization.val_injective
      simp [HomogeneousLocalization.Away.isLocalizationElem]
    rw [hloc, map_one]
  · rw [coordinateHyperplaneLocalEquation_of_ne i j hji]
    have hloc :
        HomogeneousLocalization.Away.isLocalizationElem
            (SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one R i)
            (SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one R j) =
          SpaceChart.MvPolynomial.awayVar R i ⟨j, hji⟩ := by
      apply HomogeneousLocalization.val_injective
      simp [HomogeneousLocalization.Away.isLocalizationElem, SpaceChart.MvPolynomial.awayVar]
    rw [hloc]

/-- The standard-chart local equation generates the coordinate-hyperplane
ideal. -/
lemma coordinateHyperplaneLocalEquation_span (i j : σ) :
    (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j).ker.ideal
        ⟨MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i, MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen i⟩ =
      Ideal.span {coordinateHyperplaneLocalEquation (R := R) i j} := by
  by_cases hji : j = i
  · subst i
    rw [SpaceHyperplane.MvPolynomial.coordinateHyperplaneι_ker_ideal_coordinateOpen_self,
      coordinateHyperplaneLocalEquation_self, Ideal.span_singleton_one]
  · rw [coordinateHyperplaneLocalEquation_of_ne i j hji]
    exact SpaceHyperplane.MvPolynomial.coordinateHyperplaneι_ker_ideal_coordinateOpen_of_ne i j hji

/-- The standard-chart local equation of a coordinate hyperplane is a
nonzerodivisor. -/
lemma coordinateHyperplaneLocalEquation_mem_nonZeroDivisors (i j : σ) :
    coordinateHyperplaneLocalEquation (R := R) i j ∈
      nonZeroDivisors
        Γ(Proj (homogeneousSubmodule σ R), MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) := by
  classical
  by_cases hji : j = i
  · subst i
    rw [coordinateHyperplaneLocalEquation_self]
    exact Submonoid.one_mem _
  · rw [coordinateHyperplaneLocalEquation_of_ne i j hji]
    let e := (Proj.basicOpenIsoAway (homogeneousSubmodule σ R) (X i)
      (SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one R i) one_pos).commRingCatIsoToRingEquiv
    change e (SpaceChart.MvPolynomial.awayVar R i ⟨j, hji⟩) ∈
      nonZeroDivisors Γ(Proj (homogeneousSubmodule σ R), MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
    rw [← MulEquivClass.map_nonZeroDivisors e]
    exact ⟨SpaceChart.MvPolynomial.awayVar R i ⟨j, hji⟩, SpaceChart.MvPolynomial.awayVar_mem_nonZeroDivisors R i ⟨j, hji⟩, rfl⟩

private noncomputable def coordinateHyperplaneLocalEquationAway (i j : σ) :
    HomogeneousLocalization.Away (homogeneousSubmodule σ R) (X i) := by
  classical
  exact if hji : j = i then 1 else SpaceChart.MvPolynomial.awayVar R i ⟨j, hji⟩

private noncomputable def coordinateLeftAwayMap (i k : σ) :
    HomogeneousLocalization.Away (homogeneousSubmodule σ R) (X i) →+*
      HomogeneousLocalization.Away (homogeneousSubmodule σ R) (X i * X k) :=
  HomogeneousLocalization.awayMap (homogeneousSubmodule σ R)
    (SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one R k) rfl

private noncomputable def coordinateRightAwayMap (i k : σ) :
    HomogeneousLocalization.Away (homogeneousSubmodule σ R) (X k) →+*
      HomogeneousLocalization.Away (homogeneousSubmodule σ R) (X i * X k) :=
  HomogeneousLocalization.awayMap (homogeneousSubmodule σ R)
    (SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one R i) (mul_comm _ _)

private lemma coordinateHyperplaneLocalEquationAway_map (i k j : σ) :
    coordinateLeftAwayMap (R := R) i k
        (coordinateHyperplaneLocalEquationAway (R := R) i j) =
      coordinateLeftAwayMap (R := R) i k
          (coordinateHyperplaneLocalEquationAway (R := R) i k) *
        coordinateRightAwayMap (R := R) i k
          (coordinateHyperplaneLocalEquationAway (R := R) k j) := by
  classical
  by_cases hki : k = i
  · subst k
    have hmaps : coordinateLeftAwayMap (R := R) i i =
        coordinateRightAwayMap (R := R) i i := rfl
    rw [← hmaps]
    simp [coordinateHyperplaneLocalEquationAway]
  · by_cases hji : j = i
    · subst j
      rw [show coordinateHyperplaneLocalEquationAway (R := R) i i = 1 by
        simp [coordinateHyperplaneLocalEquationAway]]
      rw [show coordinateHyperplaneLocalEquationAway (R := R) i k =
          SpaceChart.MvPolynomial.awayVar R i ⟨k, hki⟩ by
        simp [coordinateHyperplaneLocalEquationAway, hki]]
      rw [show coordinateHyperplaneLocalEquationAway (R := R) k i =
          SpaceChart.MvPolynomial.awayVar R k ⟨i, Ne.symm hki⟩ by
        simp [coordinateHyperplaneLocalEquationAway, Ne.symm hki]]
      simp only [map_one]
      apply HomogeneousLocalization.val_injective
      simp only [coordinateLeftAwayMap, coordinateRightAwayMap, SpaceChart.MvPolynomial.awayVar]
      rw [HomogeneousLocalization.awayMap_mk,
        HomogeneousLocalization.awayMap_mk,
        HomogeneousLocalization.val_mul,
        HomogeneousLocalization.Away.val_mk,
        HomogeneousLocalization.Away.val_mk]
      rw [HomogeneousLocalization.val_one, Localization.mk_mul,
        ← Localization.mk_one, Localization.mk_eq_mk_iff,
        Localization.r_iff_exists]
      exact ⟨1, by simp; ring⟩
    · by_cases hjk : j = k
      · subst j
        simp [coordinateHyperplaneLocalEquationAway, hki]
      · rw [show coordinateHyperplaneLocalEquationAway (R := R) i j =
            SpaceChart.MvPolynomial.awayVar R i ⟨j, hji⟩ by
          simp [coordinateHyperplaneLocalEquationAway, hji]]
        rw [show coordinateHyperplaneLocalEquationAway (R := R) i k =
            SpaceChart.MvPolynomial.awayVar R i ⟨k, hki⟩ by
          simp [coordinateHyperplaneLocalEquationAway, hki]]
        rw [show coordinateHyperplaneLocalEquationAway (R := R) k j =
            SpaceChart.MvPolynomial.awayVar R k ⟨j, hjk⟩ by
          simp [coordinateHyperplaneLocalEquationAway, hjk]]
        apply HomogeneousLocalization.val_injective
        simp only [coordinateLeftAwayMap, coordinateRightAwayMap, SpaceChart.MvPolynomial.awayVar]
        rw [HomogeneousLocalization.awayMap_mk,
          HomogeneousLocalization.awayMap_mk,
          HomogeneousLocalization.awayMap_mk,
          HomogeneousLocalization.val_mul,
          HomogeneousLocalization.Away.val_mk,
          HomogeneousLocalization.Away.val_mk,
          HomogeneousLocalization.Away.val_mk]
        rw [Localization.mk_mul, Localization.mk_eq_mk_iff,
          Localization.r_iff_exists]
        exact ⟨1, by simp; ring⟩

private lemma coordinateHyperplaneLocalEquation_eq_awayToSection (i j : σ) :
    coordinateHyperplaneLocalEquation (R := R) i j =
      (Proj.awayToSection (homogeneousSubmodule σ R) (X i)).hom
        (coordinateHyperplaneLocalEquationAway (R := R) i j) := by
  classical
  by_cases hji : j = i
  · subst j
    simp [coordinateHyperplaneLocalEquation,
      coordinateHyperplaneLocalEquationAway]
  · simp [coordinateHyperplaneLocalEquation,
      coordinateHyperplaneLocalEquationAway, hji,
      Proj.basicOpenIsoAway]

/-- The canonical affine presentation of the overlap of two standard
coordinate opens. -/
abbrev coordinateOpenOverlap (i k : σ) :
    (Proj (homogeneousSubmodule σ R)).Opens :=
  Proj.basicOpen (homogeneousSubmodule σ R) (X i * X k)

/-- The canonical affine coordinate overlap is the intersection of the two
standard coordinate opens. -/
lemma coordinateOpenOverlap_eq (i k : σ) :
    coordinateOpenOverlap (R := R) i k =
      MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i ⊓ MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) k :=
  Proj.basicOpen_mul (homogeneousSubmodule σ R) (X i) (X k)

/-- On the `i`-th standard chart, the principal open cut out by the `j`-th
coordinate ratio is the overlap with the `j`-th standard chart. -/
lemma coordinateHyperplaneLocalEquation_basicOpen (i j : σ) :
    (Proj (homogeneousSubmodule σ R)).basicOpen
        (coordinateHyperplaneLocalEquation (R := R) i j) =
      coordinateOpenOverlap (R := R) i j := by
  let A := homogeneousSubmodule σ R
  have hi : X i ∈ A 1 := SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one R i
  have hj : X j ∈ A 1 := SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one R j
  let U : (Proj A).Opens := MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i
  let e := Proj.basicOpenIsoSpec A (X i) hi one_pos
  let a : HomogeneousLocalization.Away A (X i) :=
    HomogeneousLocalization.Away.isLocalizationElem hi hj
  have hchart :
      U.toScheme.basicOpen
          (U.topIso.inv (coordinateHyperplaneLocalEquation (R := R) i j)) =
        U.ι ⁻¹ᵁ MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j := by
    calc
      _ = e.hom ⁻¹ᵁ
          (Spec (CommRingCat.of
            (HomogeneousLocalization.Away A (X i)))).basicOpen
              ((Scheme.ΓSpecIso _).inv a) := by
        rw [Scheme.preimage_basicOpen_top]
        apply congrArg U.toScheme.basicOpen
        change U.topIso.inv
            (coordinateHyperplaneLocalEquation (R := R) i j) =
          (Proj.basicOpenToSpec A (X i)).appTop
            ((Scheme.ΓSpecIso _).inv a)
        rw [show (Proj.basicOpenToSpec A (X i)).appTop =
            (Scheme.ΓSpecIso _).hom ≫ Proj.awayToSection A (X i) ≫
              U.topIso.inv from Proj.basicOpenToSpec_app_top A (X i)]
        simp only [CommRingCat.comp_apply, Iso.inv_hom_id_apply]
        rw [show Proj.awayToSection A (X i) =
            (Proj.basicOpenIsoAway A (X i)
              (SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one R i) one_pos).hom from rfl]
        exact congrArg U.topIso.inv
          (coordinateHyperplaneLocalEquation_eq_isLocalizationElem
            (R := R) i j)
      _ = e.hom ⁻¹ᵁ
          (Proj.awayι A (X i)
            hi one_pos ⁻¹ᵁ
              MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j) := by
        rw [basicOpen_eq_of_affine,
          Proj.awayι_preimage_basicOpen A
          hi one_pos hj one_pos]
      _ = U.ι ⁻¹ᵁ MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j := by
        rw [← Scheme.Hom.comp_preimage]
        rw [← Proj.basicOpenIsoSpec_inv_ι A (X i)
          hi one_pos]
        simp [e, U, A]
  calc
    _ = U.ι ''ᵁ U.toScheme.basicOpen
        (U.topIso.inv (coordinateHyperplaneLocalEquation (R := R) i j)) :=
      (U.ι_image_basicOpen_topIso_inv
        (coordinateHyperplaneLocalEquation (R := R) i j)).symm
    _ = U.ι ''ᵁ (U.ι ⁻¹ᵁ MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j) := by rw [hchart]
    _ = U ⊓ MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
      simp [U]
    _ = coordinateOpenOverlap (R := R) i j := by
      rw [coordinateOpenOverlap_eq]

/-- The canonical coordinate overlap is contained in its left chart. -/
lemma coordinateOpenOverlap_le_left (i k : σ) :
    coordinateOpenOverlap (R := R) i k ≤ MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i :=
  (coordinateOpenOverlap_eq (R := R) i k).trans_le inf_le_left

/-- The canonical coordinate overlap is contained in its right chart. -/
lemma coordinateOpenOverlap_le_right (i k : σ) :
    coordinateOpenOverlap (R := R) i k ≤ MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) k :=
  (coordinateOpenOverlap_eq (R := R) i k).trans_le inf_le_right

/-- Within a standard-coordinate overlap, the basic open cut out by a third coordinate
ratio is its intersection with the third standard chart. -/
lemma coordinateOpenOverlap_basicOpen_localEquation (i k j : σ) :
    (Proj (homogeneousSubmodule σ R)).basicOpen
        ((Proj (homogeneousSubmodule σ R)).presheaf.map
          (homOfLE (coordinateOpenOverlap_le_left (R := R) i k)).op
          (coordinateHyperplaneLocalEquation (R := R) i j)) =
      coordinateOpenOverlap (R := R) i k ⊓ MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j := by
  rw [Scheme.basicOpen_res,
    coordinateHyperplaneLocalEquation_basicOpen,
    coordinateOpenOverlap_eq, coordinateOpenOverlap_eq]
  ac_rfl

/-- A section on one standard coordinate chart extends to any other chart after its overlap
restriction is multiplied by a power of the corresponding coordinate ratio. -/
lemma exists_coordinateChartExtension
    (M : (Proj (homogeneousSubmodule σ R)).Modules) [M.IsQuasicoherent]
    (i j : σ) (s : Γ(M, MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j)) :
    ∃ (n : ℕ) (t : Γ(M, MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)),
      M.presheaf.map
          (homOfLE (coordinateOpenOverlap_le_left (R := R) i j)).op t =
        (Proj (homogeneousSubmodule σ R)).presheaf.map
              (homOfLE (coordinateOpenOverlap_le_left (R := R) i j)).op
              (coordinateHyperplaneLocalEquation (R := R) i j ^ n) •
          M.presheaf.map
            (homOfLE (coordinateOpenOverlap_le_right (R := R) i j)).op s := by
  let X := Proj (homogeneousSubmodule σ R)
  let U : X.affineOpens :=
    ⟨MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i, MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen (R := R) i⟩
  let f := coordinateHyperplaneLocalEquation (R := R) i j
  have hV : X.basicOpen f = coordinateOpenOverlap (R := R) i j :=
    coordinateHyperplaneLocalEquation_basicOpen (R := R) i j
  let e : Γ(M, coordinateOpenOverlap (R := R) i j) ≅
      Γ(M, X.basicOpen f) :=
    M.presheaf.mapIso (eqToIso hV).op
  let r : Γ(M, X.basicOpen f) :=
    e.hom (M.presheaf.map
      (homOfLE (coordinateOpenOverlap_le_right (R := R) i j)).op s)
  obtain ⟨n, t, ht⟩ :=
    Quasicoherent.Scheme.Modules.exists_restrict_eq_pow_smul_of_isQuasicoherent_of_isAffineOpen
      M U f r
  refine ⟨n, t, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso e.hom).1
  have hleft :
      e.hom
          (M.presheaf.map
            (homOfLE (coordinateOpenOverlap_le_left (R := R) i j)).op t) =
        M.presheaf.map (homOfLE (X.basicOpen_le f)).op t := by
    simp only [e, Functor.mapIso_hom, ← M.presheaf.map_comp_apply]
    exact ConcreteCategory.congr_hom
      (M.presheaf.congr_map (Subsingleton.elim _ _)) _
  have hright :
      e.hom
          ((Proj (homogeneousSubmodule σ R)).presheaf.map
                (homOfLE (coordinateOpenOverlap_le_left (R := R) i j)).op
                (coordinateHyperplaneLocalEquation (R := R) i j ^ n) •
            M.presheaf.map
              (homOfLE (coordinateOpenOverlap_le_right (R := R) i j)).op s) =
        X.presheaf.map (homOfLE (X.basicOpen_le f)).op (f ^ n) • r := by
    have hmap := M.val.map_smul (eqToIso hV).op.hom
      ((Proj (homogeneousSubmodule σ R)).presheaf.map
        (homOfLE (coordinateOpenOverlap_le_left (R := R) i j)).op
        (coordinateHyperplaneLocalEquation (R := R) i j ^ n))
      (M.presheaf.map
        (homOfLE (coordinateOpenOverlap_le_right (R := R) i j)).op s)
    refine hmap.trans ?_
    have hsection :
        M.val.map (eqToIso hV).op.hom
            (M.presheaf.map
              (homOfLE (coordinateOpenOverlap_le_right (R := R) i j)).op s) =
          r := by
      rfl
    rw [hsection]
    apply congrArg (fun a : Γ(X, X.basicOpen f) ↦ a • r)
    change X.ringCatSheaf.obj.map (eqToIso hV).op.hom
        (X.ringCatSheaf.obj.map
          (homOfLE (coordinateOpenOverlap_le_left (R := R) i j)).op
          (f ^ n)) =
      X.ringCatSheaf.obj.map (homOfLE (X.basicOpen_le f)).op (f ^ n)
    have hcomp :
        X.ringCatSheaf.obj.map
              (homOfLE (coordinateOpenOverlap_le_left (R := R) i j)).op ≫
            X.ringCatSheaf.obj.map (eqToIso hV).op.hom =
          X.ringCatSheaf.obj.map (homOfLE (X.basicOpen_le f)).op := by
      rw [← Functor.map_comp]
      exact X.ringCatSheaf.obj.congr_map (Subsingleton.elim _ _)
    exact ConcreteCategory.congr_hom hcomp (f ^ n)
  exact hleft.trans (ht.trans hright.symm)

/-- Over a finite standard coordinate cover, the chart extensions of a section may all be
chosen with one common coordinate-ratio exponent. -/
lemma exists_coordinateChartExtension_forall [Fintype σ]
    (M : (Proj (homogeneousSubmodule σ R)).Modules) [M.IsQuasicoherent]
    (j : σ) (s : Γ(M, MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j)) :
    ∃ (n : ℕ) (t : ∀ i : σ, Γ(M, MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)), ∀ i,
      M.presheaf.map
          (homOfLE (coordinateOpenOverlap_le_left (R := R) i j)).op (t i) =
        (Proj (homogeneousSubmodule σ R)).presheaf.map
              (homOfLE (coordinateOpenOverlap_le_left (R := R) i j)).op
              (coordinateHyperplaneLocalEquation (R := R) i j ^ n) •
          M.presheaf.map
            (homOfLE (coordinateOpenOverlap_le_right (R := R) i j)).op s := by
  classical
  choose n t ht using fun i ↦ exists_coordinateChartExtension M i j s
  let N := Finset.univ.sup n
  have hle (i : σ) : n i ≤ N := Finset.le_sup (Finset.mem_univ i)
  refine ⟨N, fun i ↦
    coordinateHyperplaneLocalEquation (R := R) i j ^ (N - n i) • t i,
    fun i ↦ ?_⟩
  rw [M.map_smul, ht i, ← mul_smul, ← map_mul, ← pow_add,
    Nat.sub_add_cancel (hle i)]

/-- If a global section of a quasicoherent module vanishes on one standard
coordinate chart, then its restriction to any other chart is annihilated by
some power of the corresponding coordinate ratio. -/
lemma exists_pow_coordinateHyperplaneLocalEquation_smul_restrict_eq_zero
    (M : (Proj (homogeneousSubmodule σ R)).Modules) [M.IsQuasicoherent]
    (i j : σ) (t : Γ(M, ⊤))
    (ht : M.presheaf.map (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j).leTop.op t = 0) :
    ∃ n : ℕ,
      coordinateHyperplaneLocalEquation (R := R) i j ^ n •
        M.presheaf.map (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i).leTop.op t = 0 := by
  let X := Proj (homogeneousSubmodule σ R)
  let U : X.affineOpens :=
    ⟨MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i, MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen (R := R) i⟩
  let V : X.Opens :=
    X.basicOpen (coordinateHyperplaneLocalEquation (R := R) i j)
  have hVi : V ≤ U.1 := X.basicOpen_le _
  have hVj : V ≤ MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j := by
    change X.basicOpen (coordinateHyperplaneLocalEquation (R := R) i j) ≤
      MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j
    rw [coordinateHyperplaneLocalEquation_basicOpen]
    exact coordinateOpenOverlap_le_right (R := R) i j
  have hi :
      M.presheaf.map (homOfLE hVi).op
          (M.presheaf.map U.1.leTop.op t) =
        M.presheaf.map V.leTop.op t := by
    rw [← M.presheaf.map_comp_apply]
    congr 1
  have hj :
      M.presheaf.map (homOfLE hVj).op
          (M.presheaf.map (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j).leTop.op t) =
        M.presheaf.map V.leTop.op t := by
    rw [← M.presheaf.map_comp_apply]
    congr 1
  apply
    Quasicoherent.Scheme.Modules.exists_pow_smul_eq_zero_of_restrict_eq_zero_of_isQuasicoherent_of_isAffineOpen
      M U (coordinateHyperplaneLocalEquation (R := R) i j)
        (M.presheaf.map U.1.leTop.op t)
  change M.presheaf.map (homOfLE hVi).op
      (M.presheaf.map U.1.leTop.op t) = 0
  rw [hi, ← hj, ht, map_zero]

/-- For a finite standard coordinate cover, the chartwise annihilating powers
of a coordinate ratio may be replaced by one common exponent. -/
lemma exists_pow_coordinateHyperplaneLocalEquation_smul_restrict_eq_zero_forall
    [Fintype σ]
    (M : (Proj (homogeneousSubmodule σ R)).Modules) [M.IsQuasicoherent]
    (j : σ) (t : Γ(M, ⊤))
    (ht : M.presheaf.map (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j).leTop.op t = 0) :
    ∃ n : ℕ, ∀ i : σ,
      coordinateHyperplaneLocalEquation (R := R) i j ^ n •
        M.presheaf.map (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i).leTop.op t = 0 := by
  classical
  choose e he using fun i ↦
    exists_pow_coordinateHyperplaneLocalEquation_smul_restrict_eq_zero
      M i j t ht
  let n := Finset.univ.sup e
  refine ⟨n, fun i ↦ ?_⟩
  have hle : e i ≤ n := Finset.le_sup (Finset.mem_univ i)
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
  rw [hd, pow_add, mul_comm, mul_smul, he i, smul_zero]

private lemma coordinateHyperplaneLocalEquation_restrict_product
    (i k j : σ) :
    (Proj (homogeneousSubmodule σ R)).presheaf.map
        (homOfLE (coordinateOpenOverlap_le_left (R := R) i k)).op
        (coordinateHyperplaneLocalEquation (R := R) i j) =
      (Proj (homogeneousSubmodule σ R)).presheaf.map
          (homOfLE (coordinateOpenOverlap_le_left (R := R) i k)).op
          (coordinateHyperplaneLocalEquation (R := R) i k) *
        (Proj (homogeneousSubmodule σ R)).presheaf.map
          (homOfLE (coordinateOpenOverlap_le_right (R := R) i k)).op
          (coordinateHyperplaneLocalEquation (R := R) k j) := by
  rw [coordinateHyperplaneLocalEquation_eq_awayToSection,
    coordinateHyperplaneLocalEquation_eq_awayToSection,
    coordinateHyperplaneLocalEquation_eq_awayToSection]
  have hleft := Proj.awayMap_awayToSection
    (homogeneousSubmodule σ R) (SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one R k)
      (rfl : X i * X k = X i * X k)
  have hleftApply := congrArg
    (fun q ↦ q.hom (coordinateHyperplaneLocalEquationAway (R := R) i j)) hleft
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
    CommRingCat.hom_ofHom] at hleftApply
  have htransitionApply := congrArg
    (fun q ↦ q.hom (coordinateHyperplaneLocalEquationAway (R := R) i k)) hleft
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
    CommRingCat.hom_ofHom] at htransitionApply
  have hright := Proj.awayMap_awayToSection
    (homogeneousSubmodule σ R) (SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one R i)
      (mul_comm (X i) (X k))
  have hrightApply := congrArg
    (fun q ↦ q.hom (coordinateHyperplaneLocalEquationAway (R := R) k j)) hright
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
    CommRingCat.hom_ofHom] at hrightApply
  rw [← hleftApply, ← htransitionApply, ← hrightApply]
  change (Proj.awayToSection (homogeneousSubmodule σ R) (X i * X k)).hom
      (coordinateLeftAwayMap (R := R) i k
        (coordinateHyperplaneLocalEquationAway (R := R) i j)) =
    (Proj.awayToSection (homogeneousSubmodule σ R) (X i * X k)).hom
        (coordinateLeftAwayMap (R := R) i k
          (coordinateHyperplaneLocalEquationAway (R := R) i k)) *
      (Proj.awayToSection (homogeneousSubmodule σ R) (X i * X k)).hom
        (coordinateRightAwayMap (R := R) i k
          (coordinateHyperplaneLocalEquationAway (R := R) k j))
  rw [← map_mul]
  exact congrArg
    (Proj.awayToSection (homogeneousSubmodule σ R) (X i * X k)).hom
    (coordinateHyperplaneLocalEquationAway_map (R := R) i k j)

/-- The unit `X_k / X_i` on the overlap of the `i`th and `k`th standard
coordinate opens. -/
noncomputable def coordinateOpenTransitionUnit (i k : σ) :
    Γ(Proj (homogeneousSubmodule σ R), coordinateOpenOverlap (R := R) i k)ˣ where
  val := (Proj (homogeneousSubmodule σ R)).presheaf.map
    (homOfLE (coordinateOpenOverlap_le_left (R := R) i k)).op
    (coordinateHyperplaneLocalEquation (R := R) i k)
  inv := (Proj (homogeneousSubmodule σ R)).presheaf.map
    (homOfLE (coordinateOpenOverlap_le_right (R := R) i k)).op
    (coordinateHyperplaneLocalEquation (R := R) k i)
  val_inv := by
    simpa [coordinateHyperplaneLocalEquation_self] using
      (coordinateHyperplaneLocalEquation_restrict_product (R := R) i k i).symm
  inv_val := by
    calc
      _ = (Proj (homogeneousSubmodule σ R)).presheaf.map
            (homOfLE (coordinateOpenOverlap_le_left (R := R) i k)).op
            (coordinateHyperplaneLocalEquation (R := R) i k) *
          (Proj (homogeneousSubmodule σ R)).presheaf.map
            (homOfLE (coordinateOpenOverlap_le_right (R := R) i k)).op
            (coordinateHyperplaneLocalEquation (R := R) k i) := mul_comm _ _
      _ = 1 := by
        simpa [coordinateHyperplaneLocalEquation_self] using
          (coordinateHyperplaneLocalEquation_restrict_product (R := R) i k i).symm

/-- On a standard-coordinate overlap, every coordinate-hyperplane local
equation changes by the unit `X_k / X_i`. -/
lemma coordinateHyperplaneLocalEquation_restrict_eq_transition_mul (i k j : σ) :
    (Proj (homogeneousSubmodule σ R)).presheaf.map
        (homOfLE (coordinateOpenOverlap_le_left (R := R) i k)).op
        (coordinateHyperplaneLocalEquation (R := R) i j) =
      (coordinateOpenTransitionUnit (R := R) i k :
          Γ(Proj (homogeneousSubmodule σ R), coordinateOpenOverlap (R := R) i k)) *
        (Proj (homogeneousSubmodule σ R)).presheaf.map
          (homOfLE (coordinateOpenOverlap_le_right (R := R) i k)).op
          (coordinateHyperplaneLocalEquation (R := R) k j) :=
  coordinateHyperplaneLocalEquation_restrict_product (R := R) i k j

/-- Two common-degree chart extensions of the same section agree up to the standard
transition factor after multiplication by a power of the coordinate cutting out the
triple overlap. -/
lemma exists_pow_coordinateChartDifference_eq_zero
    (M : (Proj (homogeneousSubmodule σ R)).Modules) [M.IsQuasicoherent]
    (i k j : σ) (n : ℕ)
    (s : Γ(M, MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j))
    (tI : Γ(M, MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i))
    (tK : Γ(M, MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) k))
    (hI : M.presheaf.map
          (homOfLE (coordinateOpenOverlap_le_left (R := R) i j)).op tI =
        (Proj (homogeneousSubmodule σ R)).presheaf.map
              (homOfLE (coordinateOpenOverlap_le_left (R := R) i j)).op
              (coordinateHyperplaneLocalEquation (R := R) i j ^ n) •
          M.presheaf.map
            (homOfLE (coordinateOpenOverlap_le_right (R := R) i j)).op s)
    (hK : M.presheaf.map
          (homOfLE (coordinateOpenOverlap_le_left (R := R) k j)).op tK =
        (Proj (homogeneousSubmodule σ R)).presheaf.map
              (homOfLE (coordinateOpenOverlap_le_left (R := R) k j)).op
              (coordinateHyperplaneLocalEquation (R := R) k j ^ n) •
          M.presheaf.map
            (homOfLE (coordinateOpenOverlap_le_right (R := R) k j)).op s) :
    ∃ m : ℕ,
      ((Proj (homogeneousSubmodule σ R)).presheaf.map
          (homOfLE (coordinateOpenOverlap_le_left (R := R) i k)).op
          (coordinateHyperplaneLocalEquation (R := R) i j)) ^ m •
        (M.presheaf.map
            (homOfLE (coordinateOpenOverlap_le_left (R := R) i k)).op tI -
          (coordinateOpenTransitionUnit (R := R) i k :
              Γ(Proj (homogeneousSubmodule σ R),
                coordinateOpenOverlap (R := R) i k)) ^ n •
            M.presheaf.map
              (homOfLE (coordinateOpenOverlap_le_right (R := R) i k)).op tK) = 0 := by
  let Xp := Proj (homogeneousSubmodule σ R)
  let W := coordinateOpenOverlap (R := R) i k
  let r : Γ(Xp, W) := Xp.presheaf.map
    (homOfLE (coordinateOpenOverlap_le_left (R := R) i k)).op
    (coordinateHyperplaneLocalEquation (R := R) i j)
  let d : Γ(M, W) := M.presheaf.map
      (homOfLE (coordinateOpenOverlap_le_left (R := R) i k)).op tI -
    (coordinateOpenTransitionUnit (R := R) i k : Γ(Xp, W)) ^ n •
      M.presheaf.map
        (homOfLE (coordinateOpenOverlap_le_right (R := R) i k)).op tK
  have hW : IsAffineOpen W :=
    Proj.isAffineOpen_basicOpen (homogeneousSubmodule σ R) (X i * X k)
      (SetLike.mul_mem_graded
        (SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one R i)
        (SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one R k)) (by omega)
  let U : Xp.affineOpens := ⟨W, hW⟩
  apply
    Quasicoherent.Scheme.Modules.exists_pow_smul_eq_zero_of_restrict_eq_zero_of_isQuasicoherent_of_isAffineOpen
      M U r d
  let V := Xp.basicOpen r
  have hV : V = W ⊓ MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j :=
    coordinateOpenOverlap_basicOpen_localEquation (R := R) i k j
  have hVI : V ≤ coordinateOpenOverlap (R := R) i j := by
    rw [hV]
    dsimp only [W]
    rw [coordinateOpenOverlap_eq, coordinateOpenOverlap_eq]
    exact le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have hVK : V ≤ coordinateOpenOverlap (R := R) k j := by
    rw [hV]
    dsimp only [W]
    rw [coordinateOpenOverlap_eq, coordinateOpenOverlap_eq]
    exact le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have hMcomp : ∀ {A B C : Xp.Opens} (hBA : B ≤ A) (hCB : C ≤ B)
      (x : Γ(M, A)),
      M.presheaf.map (homOfLE hCB).op
          (M.presheaf.map (homOfLE hBA).op x) =
        M.presheaf.map (homOfLE (hCB.trans hBA)).op x := by
    intro A B C hBA hCB x
    rw [← M.presheaf.map_comp_apply]
    exact ConcreteCategory.congr_hom
      (M.presheaf.congr_map (Subsingleton.elim _ _)) x
  have hXcomp : ∀ {A B C : Xp.Opens} (hBA : B ≤ A) (hCB : C ≤ B)
      (x : Γ(Xp, A)),
      Xp.presheaf.map (homOfLE hCB).op
          (Xp.presheaf.map (homOfLE hBA).op x) =
        Xp.presheaf.map (homOfLE (hCB.trans hBA)).op x := by
    intro A B C hBA hCB x
    rw [← Xp.presheaf.map_comp_apply]
    exact ConcreteCategory.congr_hom
      (Xp.presheaf.congr_map (Subsingleton.elim _ _)) x
  have hI' := congrArg (M.presheaf.map (homOfLE hVI).op) hI
  rw [M.map_smul, hMcomp, hXcomp, hMcomp] at hI'
  have hK' := congrArg (M.presheaf.map (homOfLE hVK).op) hK
  rw [M.map_smul, hMcomp, hXcomp, hMcomp] at hK'
  change M.presheaf.map (homOfLE (Xp.basicOpen_le r)).op d = 0
  dsimp only [d]
  rw [map_sub, M.map_smul, hMcomp, map_pow, hMcomp]
  rw [hI', hK']
  have hr := congrArg
    (Xp.presheaf.map (homOfLE (Xp.basicOpen_le r)).op)
    (coordinateHyperplaneLocalEquation_restrict_eq_transition_mul
      (R := R) i k j)
  rw [map_mul, hXcomp, hXcomp] at hr
  rw [map_pow, map_pow]
  rw [hr, mul_pow, mul_smul, sub_self]

/-- Over a finite standard coordinate cover, all transition-adjusted differences between
common-degree chart extensions are annihilated by one common coordinate power. -/
lemma exists_pow_coordinateChartDifference_eq_zero_forall [Fintype σ]
    (M : (Proj (homogeneousSubmodule σ R)).Modules) [M.IsQuasicoherent]
    (j : σ) (n : ℕ)
    (s : Γ(M, MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j))
    (t : ∀ i : σ, Γ(M, MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i))
    (ht : ∀ i,
      M.presheaf.map
          (homOfLE (coordinateOpenOverlap_le_left (R := R) i j)).op (t i) =
        (Proj (homogeneousSubmodule σ R)).presheaf.map
              (homOfLE (coordinateOpenOverlap_le_left (R := R) i j)).op
              (coordinateHyperplaneLocalEquation (R := R) i j ^ n) •
          M.presheaf.map
            (homOfLE (coordinateOpenOverlap_le_right (R := R) i j)).op s) :
    ∃ m : ℕ, ∀ i k : σ,
      ((Proj (homogeneousSubmodule σ R)).presheaf.map
          (homOfLE (coordinateOpenOverlap_le_left (R := R) i k)).op
          (coordinateHyperplaneLocalEquation (R := R) i j)) ^ m •
        (M.presheaf.map
            (homOfLE (coordinateOpenOverlap_le_left (R := R) i k)).op (t i) -
          (coordinateOpenTransitionUnit (R := R) i k :
              Γ(Proj (homogeneousSubmodule σ R),
                coordinateOpenOverlap (R := R) i k)) ^ n •
            M.presheaf.map
              (homOfLE (coordinateOpenOverlap_le_right (R := R) i k)).op (t k)) = 0 := by
  classical
  choose e he using fun p : σ × σ ↦
    exists_pow_coordinateChartDifference_eq_zero
      M p.1 p.2 j n s (t p.1) (t p.2) (ht p.1) (ht p.2)
  let m := Finset.univ.sup e
  refine ⟨m, fun i k ↦ ?_⟩
  have hle : e (i, k) ≤ m := Finset.le_sup (Finset.mem_univ (i, k))
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
  rw [hd, pow_add, mul_comm, mul_smul, he (i, k), smul_zero]

/-- Multiplying two chart extensions by the common annihilating coordinate power
turns their degree-`n` compatibility modulo torsion into exact degree-`n + m`
compatibility. -/
lemma coordinateChartExtensions_corrected_compatible
    (M : (Proj (homogeneousSubmodule σ R)).Modules)
    (i k j : σ) (n m : ℕ)
    (tI : Γ(M, MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i))
    (tK : Γ(M, MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) k))
    (h :
      ((Proj (homogeneousSubmodule σ R)).presheaf.map
          (homOfLE (coordinateOpenOverlap_le_left (R := R) i k)).op
          (coordinateHyperplaneLocalEquation (R := R) i j)) ^ m •
        (M.presheaf.map
            (homOfLE (coordinateOpenOverlap_le_left (R := R) i k)).op tI -
          (coordinateOpenTransitionUnit (R := R) i k :
              Γ(Proj (homogeneousSubmodule σ R),
                coordinateOpenOverlap (R := R) i k)) ^ n •
            M.presheaf.map
              (homOfLE (coordinateOpenOverlap_le_right (R := R) i k)).op tK) = 0) :
    M.presheaf.map
        (homOfLE (coordinateOpenOverlap_le_left (R := R) i k)).op
        (coordinateHyperplaneLocalEquation (R := R) i j ^ m • tI) =
      (coordinateOpenTransitionUnit (R := R) i k :
          Γ(Proj (homogeneousSubmodule σ R),
            coordinateOpenOverlap (R := R) i k)) ^ (n + m) •
        M.presheaf.map
          (homOfLE (coordinateOpenOverlap_le_right (R := R) i k)).op
          (coordinateHyperplaneLocalEquation (R := R) k j ^ m • tK) := by
  let Xp := Proj (homogeneousSubmodule σ R)
  let W := coordinateOpenOverlap (R := R) i k
  let r : Γ(Xp, W) := Xp.presheaf.map
    (homOfLE (coordinateOpenOverlap_le_left (R := R) i k)).op
    (coordinateHyperplaneLocalEquation (R := R) i j)
  let q : Γ(Xp, W) := Xp.presheaf.map
    (homOfLE (coordinateOpenOverlap_le_right (R := R) i k)).op
    (coordinateHyperplaneLocalEquation (R := R) k j)
  let u : Γ(Xp, W) := coordinateOpenTransitionUnit (R := R) i k
  let a : Γ(M, W) := M.presheaf.map
    (homOfLE (coordinateOpenOverlap_le_left (R := R) i k)).op tI
  let b : Γ(M, W) := M.presheaf.map
    (homOfLE (coordinateOpenOverlap_le_right (R := R) i k)).op tK
  have hr : r = u * q :=
    coordinateHyperplaneLocalEquation_restrict_eq_transition_mul
      (R := R) i k j
  have hab : r ^ m • a = r ^ m • (u ^ n • b) := by
    apply sub_eq_zero.mp
    rw [← smul_sub]
    exact h
  have hscalar : r ^ m * u ^ n = u ^ (n + m) * q ^ m := by
    rw [hr, mul_pow, pow_add]
    ring
  calc
    _ = r ^ m • a := by rw [M.map_smul, map_pow]
    _ = r ^ m • (u ^ n • b) := hab
    _ = (r ^ m * u ^ n) • b := by rw [mul_smul]
    _ = (u ^ (n + m) * q ^ m) • b := by rw [hscalar]
    _ = u ^ (n + m) • (q ^ m • b) := by rw [mul_smul]
    _ = _ := by rw [M.map_smul, map_pow]

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial
