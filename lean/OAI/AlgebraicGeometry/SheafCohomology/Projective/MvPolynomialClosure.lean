/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.
This file has been modified.
-/
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.RingTheory.MvPolynomial.Ideal
import OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedQuotient
import OAI.AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialHomogenize
import OAI.AlgebraicGeometry.SheafCohomology.Projective.ClosedImmersion
import OAI.AlgebraicGeometry.SheafCohomology.Projective.ToSpecZero
import OAI.AlgebraicGeometry.SheafCohomology.Projective.SpaceChart

/-! # Mv Polynomial Closure -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial

noncomputable section

open _root_.MvPolynomial

/-

ForMathlib (OURS, not vendored): upstream candidate.
-/

/-!
# Projective closures from homogenized relations

A family of affine polynomial relations determines a homogeneous quotient after adjoining one
variable. With finitely many polynomial variables, its `Proj` is proper over the coefficient ring.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.HomogeneousIdeal _root_.HomogeneousLocalization MorphismProperty

universe u

variable {R : Type u} {σ κ : Type} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The monomials of total degree `n` form a basis of the degree-`n` homogeneous
submodule of a multivariate polynomial ring. -/
noncomputable def basisHomogeneousSubmodule (n : ℕ) :
    Module.Basis {d : σ →₀ ℕ // d.degree = n} R (homogeneousSubmodule σ R n) := by
  rw [homogeneousSubmodule_eq_finsupp_supported]
  exact basisRestrictSupport R {d : σ →₀ ℕ | d.degree = n}

/-- Every homogeneous piece of a multivariate polynomial ring is a free module over the
coefficient ring. -/
instance homogeneousSubmodule_free (n : ℕ) :
    Module.Free R (homogeneousSubmodule σ R n) :=
  Module.Free.of_basis (basisHomogeneousSubmodule n)

/-- Over finitely many variables, every homogeneous piece is finite over the coefficient ring. -/
instance homogeneousSubmodule_finite [Finite σ] (n : ℕ) :
    Module.Finite R (homogeneousSubmodule σ R n) :=
  Module.Finite.of_fg (homogeneousSubmodule_fg σ R n)

/-- The structure morphism from the polynomial `Proj` to the coefficient ring. -/
def homogeneousProjπ :
    Proj (homogeneousSubmodule σ R) ⟶ Spec (.of R) :=
  Proj.toSpecZero (homogeneousSubmodule σ R) ≫
    Spec.map (CommRingCat.ofHom
      (algebraMap R (↥(homogeneousSubmodule σ R 0))))

/-- Polynomial projective space in finitely many homogeneous coordinates is locally of finite
type over the coefficient spectrum. -/
lemma homogeneousProjπ_locallyOfFiniteType [Finite σ] :
    LocallyOfFiniteType (homogeneousProjπ (R := R) (σ := σ)) := by
  let : Algebra.FiniteType R (MvPolynomial σ R) := by infer_instance
  let : IsScalarTower R (homogeneousSubmodule σ R 0) (MvPolynomial σ R) :=
    IsScalarTower.of_algebraMap_eq'
      (R := R) (S := homogeneousSubmodule σ R 0) (A := MvPolynomial σ R)
      (by ext r; rfl)
  let : Algebra.FiniteType (homogeneousSubmodule σ R 0) (MvPolynomial σ R) :=
    Algebra.FiniteType.of_restrictScalars_finiteType R
      (homogeneousSubmodule σ R 0) (MvPolynomial σ R)
  let : Algebra.FiniteType R (homogeneousSubmodule σ R 0) := by infer_instance
  let hproj : LocallyOfFiniteType
      (Proj.toSpecZero (homogeneousSubmodule σ R)) := inferInstance
  let hbase : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom
        (algebraMap R (homogeneousSubmodule σ R 0)))) :=
    (AlgebraicGeometry.HasRingHomProperty.Spec_iff
      (P := @LocallyOfFiniteType)).mpr
        ((RingHom.finiteType_algebraMap).mpr inferInstance)
  exact IsStableUnderComposition.comp_mem _ _ hproj hbase

/-- The projective scheme cut out by a family of homogenized polynomial relations. -/
@[reducible]
def homogenizedProj (g : κ → MvPolynomial σ R) (d : κ → ℕ) : Scheme.{u} :=
  Proj (GradedQuotient.HomogeneousIdeal.quotientGrading (MvPolynomialHomogenize.MvPolynomial.homogenizedIdeal g d))

/-- The structure morphism of a homogenized projective closure to its coefficient ring. -/
def homogenizedProjπ (g : κ → MvPolynomial σ R) (d : κ → ℕ) :
    homogenizedProj g d ⟶ Spec (.of R) :=
  Proj.toSpecZero _ ≫
    Spec.map (CommRingCat.ofHom (GradedQuotient.HomogeneousIdeal.algebraMapGradeZero (MvPolynomialHomogenize.MvPolynomial.homogenizedIdeal g d)))

/-- A homogenized projective closure in finitely many variables is proper over its coefficient
ring. -/
lemma homogenizedProjπ_isProper [Finite σ] (g : κ → MvPolynomial σ R) (d : κ → ℕ) :
    IsProper (homogenizedProjπ g d) := by
  let I := MvPolynomialHomogenize.MvPolynomial.homogenizedIdeal g d
  have hfiniteR : Algebra.FiniteType R (MvPolynomial (Option σ) R ⧸ I.toIdeal) :=
    Algebra.FiniteType.of_surjective
      (Ideal.Quotient.mkₐ R I.toIdeal) (Ideal.Quotient.mkₐ_surjective R _)
  have hfiniteZero :
      Algebra.FiniteType (↥(GradedQuotient.HomogeneousIdeal.quotientGrading I 0))
        (MvPolynomial (Option σ) R ⧸ I.toIdeal) :=
    Algebra.FiniteType.of_restrictScalars_finiteType R
      (↥(GradedQuotient.HomogeneousIdeal.quotientGrading I 0)) (MvPolynomial (Option σ) R ⧸ I.toIdeal)
  have hproj : IsProper (Proj.toSpecZero (GradedQuotient.HomogeneousIdeal.quotientGrading I)) := inferInstance
  have hclosed : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (GradedQuotient.HomogeneousIdeal.algebraMapGradeZero I))) :=
    IsClosedImmersion.spec_of_surjective _
      (GradedQuotient.HomogeneousIdeal.algebraMapGradeZero_surjective_mvPolynomial I)
  have hbase : IsProper
      (Spec.map (CommRingCat.ofHom (GradedQuotient.HomogeneousIdeal.algebraMapGradeZero I))) := inferInstance
  change IsProper
    (Proj.toSpecZero (GradedQuotient.HomogeneousIdeal.quotientGrading I) ≫
      Spec.map (CommRingCat.ofHom (GradedQuotient.HomogeneousIdeal.algebraMapGradeZero I)))
  exact IsStableUnderComposition.comp_mem _ _ hproj hbase

/-- A homogenized projective closure as a closed subscheme of polynomial `Proj`. -/
def homogenizedProjι (g : κ → MvPolynomial σ R) (d : κ → ℕ) :
    homogenizedProj g d ⟶ Proj (homogeneousSubmodule (Option σ) R) :=
  Proj.map (GradedQuotient.HomogeneousIdeal.quotientGradingHom (MvPolynomialHomogenize.MvPolynomial.homogenizedIdeal g d))
    (GradedQuotient.HomogeneousIdeal.quotientGradingHom_irrelevant_le (MvPolynomialHomogenize.MvPolynomial.homogenizedIdeal g d))

/-- The projective-closure embedding is a closed immersion. -/
lemma homogenizedProjι_isClosedImmersion
    (g : κ → MvPolynomial σ R) (d : κ → ℕ) :
    IsClosedImmersion (homogenizedProjι g d) :=
  ClosedImmersion.HomogeneousIdeal.isClosedImmersion_proj_map_quotientGradingHom (MvPolynomialHomogenize.MvPolynomial.homogenizedIdeal g d)

/-- The projective-closure embedding commutes with the structure morphisms to the
coefficient ring. -/
lemma homogenizedProjι_comp_homogeneousProjπ
    (g : κ → MvPolynomial σ R) (d : κ → ℕ) :
    homogenizedProjι g d ≫ homogeneousProjπ (R := R) (σ := Option σ) =
      homogenizedProjπ g d := by
  unfold homogenizedProjι homogeneousProjπ homogenizedProjπ
  rw [← Category.assoc, ToSpecZero.map_comp_toSpecZero]
  rw [Category.assoc, ← Spec.map_comp]
  rfl

lemma irrelevant_toIdeal_le_span_range_X :
    (irrelevant (homogeneousSubmodule σ R)).toIdeal ≤
      Ideal.span (Set.range (X : σ → MvPolynomial σ R)) := by
  rw [toIdeal_irrelevant_le]
  intro n hn p hp
  change p ∈ Ideal.span (Set.range (X : σ → MvPolynomial σ R))
  rw [← idealOfVars, ← pow_one (idealOfVars σ R), mem_pow_idealOfVars_iff]
  intro m hm
  have hdegree := ((mem_homogeneousSubmodule _ _).mp hp).degree_eq_sum_deg_support hm
  have hn' : 1 ≤ n := hn
  simpa [Finsupp.degree_apply, ← hdegree] using hn'

/-- A standard coordinate open in polynomial projective space. -/
abbrev coordinateOpen (i : σ) :
    (Proj (homogeneousSubmodule σ R)).Opens :=
  Proj.basicOpen (homogeneousSubmodule σ R) (X i)

/-- Every standard coordinate open in polynomial projective space is affine. -/
lemma coordinateOpen_isAffineOpen (i : σ) :
    IsAffineOpen (coordinateOpen (R := R) i) :=
  Proj.isAffineOpen_basicOpen (homogeneousSubmodule σ R) (X i)
    (SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one R i) one_pos

/-- The standard coordinate opens cover polynomial projective space. -/
lemma iSup_coordinateOpen_eq_top :
    ⨆ i : σ, coordinateOpen (R := R) i = ⊤ := by
  apply Proj.iSup_basicOpen_eq_top
  exact irrelevant_toIdeal_le_span_range_X

/-- The standard coordinate open in the `Proj` of a homogeneous polynomial quotient. -/
abbrev quotientCoordinateOpen
    (I : HomogeneousIdeal (homogeneousSubmodule σ R)) (i : σ) :
    (Proj (GradedQuotient.HomogeneousIdeal.quotientGrading I)).Opens :=
  Proj.basicOpen (GradedQuotient.HomogeneousIdeal.quotientGrading I) (GradedQuotient.HomogeneousIdeal.quotientGradingHom I (X i))

/-- Every standard coordinate open in a homogeneous polynomial quotient is affine. -/
lemma quotientCoordinateOpen_isAffineOpen
    (I : HomogeneousIdeal (homogeneousSubmodule σ R)) (i : σ) :
    IsAffineOpen (quotientCoordinateOpen I i) :=
  Proj.isAffineOpen_basicOpen (GradedQuotient.HomogeneousIdeal.quotientGrading I) (GradedQuotient.HomogeneousIdeal.quotientGradingHom I (X i))
    (GradedQuotient.HomogeneousIdeal.mk_mem_quotientGrading I (SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one R i)) one_pos

/-- The standard coordinate opens cover the `Proj` of a homogeneous polynomial quotient. -/
lemma iSup_quotientCoordinateOpen_eq_top
    (I : HomogeneousIdeal (homogeneousSubmodule σ R)) :
    ⨆ i : σ, quotientCoordinateOpen I i = ⊤ := by
  apply Proj.iSup_basicOpen_eq_top
  calc
    (irrelevant (GradedQuotient.HomogeneousIdeal.quotientGrading I)).toIdeal ≤
        (HomogeneousIdeal.map (GradedQuotient.HomogeneousIdeal.quotientGradingHom I)
          (irrelevant (homogeneousSubmodule σ R))).toIdeal :=
      GradedQuotient.HomogeneousIdeal.quotientGradingHom_irrelevant_le I
    _ = Ideal.map (GradedQuotient.HomogeneousIdeal.quotientGradingHom I)
        (irrelevant (homogeneousSubmodule σ R)).toIdeal := rfl
    _ ≤ Ideal.map (GradedQuotient.HomogeneousIdeal.quotientGradingHom I)
        (Ideal.span (Set.range (X : σ → MvPolynomial σ R))) :=
      Ideal.map_mono irrelevant_toIdeal_le_span_range_X
    _ = Ideal.span (Set.range fun i : σ ↦ GradedQuotient.HomogeneousIdeal.quotientGradingHom I (X i)) := by
      rw [Ideal.map_span]
      congr 1
      ext x
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨X i, ⟨i, rfl⟩, rfl⟩

local instance : DecidableEq (Option σ) := Classical.decEq _

private def optionNeNoneEquiv (σ : Type*) : {x : Option σ // x ≠ none} ≃ σ where
  toFun x := x.1.get (Option.ne_none_iff_isSome.mp x.2)
  invFun x := ⟨some x, by simp⟩
  left_inv x := Subtype.ext (Option.some_get _)
  right_inv x := Option.get_some _ _

private lemma rename_dehomogenizeAux_none (p : MvPolynomial (Option σ) R) :
    rename (optionNeNoneEquiv σ) (SpaceChart.MvPolynomial.dehomogenizeAux R none p) =
      MvPolynomialHomogenize.MvPolynomial.dehomogenizeOption R p := by
  classical
  apply RingHom.congr_fun
    (f := (rename (optionNeNoneEquiv σ)).toRingHom.comp (SpaceChart.MvPolynomial.dehomogenizeAux R none))
    (g := MvPolynomialHomogenize.MvPolynomial.dehomogenizeOption R)
  refine ringHom_ext (fun r ↦ ?_) (fun i ↦ ?_)
  · simp
  · cases i with
    | none => simp
    | some i => simp [optionNeNoneEquiv]

/-- The standard projective chart at the added homogenizing variable is affine space in the
original variables. -/
noncomputable def optionChartRingEquiv :
    Away (homogeneousSubmodule (Option σ) R) (X none : MvPolynomial (Option σ) R) ≃+*
      MvPolynomial σ R := by
  classical
  exact (SpaceChart.MvPolynomial.chartRingEquiv R (none : Option σ)).trans
    (renameEquiv R (optionNeNoneEquiv σ)).toRingEquiv

private lemma optionChartRingEquiv_symm_C (r : R) :
    (optionChartRingEquiv (R := R) (σ := σ)).symm (C r) =
      SpaceChart.MvPolynomial.awayConst R (none : Option σ) r := by
  simp [optionChartRingEquiv, SpaceChart.MvPolynomial.chartRingEquiv, SpaceChart.MvPolynomial.homogenizeAt, SpaceChart.MvPolynomial.awayConst]
  rfl

/-- On a homogeneous fraction, the option chart is dehomogenization of its numerator. -/
lemma optionChartRingEquiv_apply_mk (n : ℕ) (p : MvPolynomial (Option σ) R)
    (hp : p ∈ homogeneousSubmodule (Option σ) R (n • (1 : ℕ))) :
    optionChartRingEquiv
      (Away.mk _ (SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one R (none : Option σ)) n p hp) =
      MvPolynomialHomogenize.MvPolynomial.dehomogenizeOption R p := by
  classical
  change rename (optionNeNoneEquiv σ)
      (SpaceChart.MvPolynomial.dehomogenizeAt R none
        (Away.mk _ (SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one R (none : Option σ)) n p hp)) = _
  rw [SpaceChart.MvPolynomial.dehomogenizeAt_mk, rename_dehomogenizeAux_none]

/-- Under the standard chart equivalence, a homogeneous lift divided by the homogenizing
variable to its chosen degree is the original polynomial. -/
lemma optionChartRingEquiv_apply_mk_homogenizeOption
    (p : MvPolynomial σ R) (n : ℕ) (h : p.totalDegree ≤ n) :
    optionChartRingEquiv
      (Away.mk _ (SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one R (none : Option σ)) n
        (MvPolynomialHomogenize.MvPolynomial.homogenizeOption p n)
        (by
          simpa using (mem_homogeneousSubmodule _ _).mpr
            (MvPolynomialHomogenize.MvPolynomial.homogenizeOption_isHomogeneous p n))) = p := by
  rw [optionChartRingEquiv_apply_mk,
    MvPolynomialHomogenize.MvPolynomial.dehomogenizeOption_homogenizeOption p n h]

/-- The kernel cutting out the homogenized quotient chart becomes the original affine relation
ideal under the option chart equivalence. -/
lemma map_optionChartRingEquiv_ker_awayMap_homogenizedIdeal
    (g : κ → MvPolynomial σ R) (d : κ → ℕ)
    (hdeg : ∀ j, (g j).totalDegree ≤ d j) :
    Ideal.map (optionChartRingEquiv (R := R) (σ := σ)).toRingHom
        (RingHom.ker (Away.map
          (GradedQuotient.HomogeneousIdeal.quotientGradingHom (MvPolynomialHomogenize.MvPolynomial.homogenizedIdeal (R := R) (σ := σ) g d))
          (X none : MvPolynomial (Option σ) R))) =
      Ideal.span (Set.range g) := by
  classical
  let I := MvPolynomialHomogenize.MvPolynomial.homogenizedIdeal g d
  let s : MvPolynomial (Option σ) R := X none
  let hs : s ∈ homogeneousSubmodule (Option σ) R 1 :=
    SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one R none
  let φ := Away.map (GradedQuotient.HomogeneousIdeal.quotientGradingHom I) s
  apply le_antisymm
  · intro x hx
    obtain ⟨z, hz, rfl⟩ :=
      (Ideal.mem_map_of_equiv (optionChartRingEquiv (R := R) (σ := σ)) _).mp hx
    obtain ⟨n, p, hp, rfl⟩ := Away.mk_surjective _ hs z
    rw [RingHom.mem_ker, Away.map_mk] at hz
    have hval := congrArg
      (SpaceChart.HomogeneousLocalization.valRingHom (Submonoid.powers ((GradedQuotient.HomogeneousIdeal.quotientGradingHom I) s))) hz
    rw [SpaceChart.HomogeneousLocalization.valRingHom_apply, SpaceChart.HomogeneousLocalization.valRingHom_apply, Away.val_mk, val_zero] at hval
    have hzero : algebraMap (MvPolynomial (Option σ) R ⧸ I.toIdeal)
        (Localization (Submonoid.powers ((GradedQuotient.HomogeneousIdeal.quotientGradingHom I) s)))
        ((GradedQuotient.HomogeneousIdeal.quotientGradingHom I) p) = 0 := by
      rw [← Localization.mk_one_eq_algebraMap, Localization.mk_eq_mk',
        IsLocalization.mk'_eq_zero_iff]
      rwa [Localization.mk_eq_mk', IsLocalization.mk'_eq_zero_iff] at hval
    obtain ⟨⟨c, k, rfl⟩, hc⟩ := (IsLocalization.map_eq_zero_iff
      (Submonoid.powers ((GradedQuotient.HomogeneousIdeal.quotientGradingHom I) s)) _ _).mp hzero
    have hmem : s ^ k * p ∈ I.toIdeal := by
      have : (GradedQuotient.HomogeneousIdeal.quotientGradingHom I) (s ^ k * p) = 0 := by
        rw [map_mul, map_pow]
        exact hc
      rwa [GradedQuotient.HomogeneousIdeal.quotientGradingHom_apply, ← RingHom.mem_ker, Ideal.mk_ker] at this
    have hdehom : MvPolynomialHomogenize.MvPolynomial.dehomogenizeOption R (s ^ k * p) ∈ Ideal.span (Set.range g) := by
      rw [← MvPolynomialHomogenize.MvPolynomial.map_dehomogenizeOption_homogenizedIdeal g d hdeg]
      exact Ideal.mem_map_of_mem (MvPolynomialHomogenize.MvPolynomial.dehomogenizeOption R) hmem
    rw [map_mul, map_pow, MvPolynomialHomogenize.MvPolynomial.dehomogenizeOption_X_none, one_pow, one_mul] at hdehom
    rw [optionChartRingEquiv_apply_mk (R := R) (σ := σ)]
    exact hdehom
  · rw [Ideal.span_le]
    intro p hp
    obtain ⟨j, rfl⟩ := hp
    let q := MvPolynomialHomogenize.MvPolynomial.homogenizeOption (g j) (d j)
    have hq : q ∈ homogeneousSubmodule (Option σ) R (d j) :=
      (mem_homogeneousSubmodule _ _).mpr (MvPolynomialHomogenize.MvPolynomial.homogenizeOption_isHomogeneous (g j) (d j))
    have hq' : q ∈ homogeneousSubmodule (Option σ) R ((d j) • (1 : ℕ)) := by
      simpa using hq
    let w := Away.mk _ hs (d j) q hq'
    have hw : w ∈ RingHom.ker φ := by
      rw [RingHom.mem_ker, Away.map_mk]
      have hqzero : (GradedQuotient.HomogeneousIdeal.quotientGradingHom I) q = 0 := by
        rw [GradedQuotient.HomogeneousIdeal.quotientGradingHom_apply, ← RingHom.mem_ker, Ideal.mk_ker]
        exact Ideal.subset_span ⟨j, rfl⟩
      apply val_injective
      rw [Away.val_mk, val_zero, hqzero]
      exact Localization.mk_zero _
    have he : (optionChartRingEquiv (R := R) (σ := σ)) w = g j := by
      rw [optionChartRingEquiv_apply_mk (R := R) (σ := σ),
        MvPolynomialHomogenize.MvPolynomial.dehomogenizeOption_homogenizeOption _ _ (hdeg j)]
    rw [← he]
    exact Ideal.mem_map_of_mem
      (optionChartRingEquiv (R := R) (σ := σ)).toRingHom hw

/-- The chart of a homogenized projective closure at the homogenizing coordinate is the original
affine presentation. -/
noncomputable def homogenizedChartRingEquiv
    (g : κ → MvPolynomial σ R) (d : κ → ℕ)
    (hdeg : ∀ j, (g j).totalDegree ≤ d j) :
    (MvPolynomial σ R ⧸ Ideal.span (Set.range g)) ≃+*
      Away (GradedQuotient.HomogeneousIdeal.quotientGrading (MvPolynomialHomogenize.MvPolynomial.homogenizedIdeal g d))
        ((GradedQuotient.HomogeneousIdeal.quotientGradingHom (MvPolynomialHomogenize.MvPolynomial.homogenizedIdeal g d))
          (X none : MvPolynomial (Option σ) R)) :=
  ((Ideal.quotientEquiv
    (RingHom.ker (Away.map (GradedQuotient.HomogeneousIdeal.quotientGradingHom (MvPolynomialHomogenize.MvPolynomial.homogenizedIdeal g d))
      (X none : MvPolynomial (Option σ) R)))
    (Ideal.span (Set.range g)) optionChartRingEquiv
    (map_optionChartRingEquiv_ker_awayMap_homogenizedIdeal g d hdeg).symm).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      (ClosedImmersion.HomogeneousIdeal.away_map_quotientGradingHom_surjective (MvPolynomialHomogenize.MvPolynomial.homogenizedIdeal g d)
        (SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one R (none : Option σ))))

@[simp]
lemma homogenizedChartRingEquiv_mk
    (g : κ → MvPolynomial σ R) (d : κ → ℕ)
    (hdeg : ∀ j, (g j).totalDegree ≤ d j) (p : MvPolynomial σ R) :
    homogenizedChartRingEquiv g d hdeg
        (Ideal.Quotient.mk (Ideal.span (Set.range g)) p) =
      Away.map (GradedQuotient.HomogeneousIdeal.quotientGradingHom (MvPolynomialHomogenize.MvPolynomial.homogenizedIdeal g d))
        (X none : MvPolynomial (Option σ) R) (optionChartRingEquiv.symm p) := by
  rfl

/-- The coefficient-ring algebra structure on the homogenizing-coordinate chart. -/
noncomputable instance homogenizedChartAwayAlgebra
    (g : κ → MvPolynomial σ R) (d : κ → ℕ) :
    Algebra R
      (Away (GradedQuotient.HomogeneousIdeal.quotientGrading (MvPolynomialHomogenize.MvPolynomial.homogenizedIdeal g d))
        ((GradedQuotient.HomogeneousIdeal.quotientGradingHom (MvPolynomialHomogenize.MvPolynomial.homogenizedIdeal g d))
          (X none : MvPolynomial (Option σ) R))) :=
  ((fromZeroRingHom (GradedQuotient.HomogeneousIdeal.quotientGrading (MvPolynomialHomogenize.MvPolynomial.homogenizedIdeal g d)) _).comp
    (GradedQuotient.HomogeneousIdeal.algebraMapGradeZero (MvPolynomialHomogenize.MvPolynomial.homogenizedIdeal g d))).toAlgebra

/-- The homogenized chart equivalence sends coefficient classes to coefficient sections. -/
lemma homogenizedChartRingEquiv_mk_C
    (g : κ → MvPolynomial σ R) (d : κ → ℕ)
    (hdeg : ∀ j, (g j).totalDegree ≤ d j) (r : R) :
    homogenizedChartRingEquiv g d hdeg
        (Ideal.Quotient.mk (Ideal.span (Set.range g)) (C r)) =
      algebraMap R
        (Away (GradedQuotient.HomogeneousIdeal.quotientGrading (MvPolynomialHomogenize.MvPolynomial.homogenizedIdeal g d))
          ((GradedQuotient.HomogeneousIdeal.quotientGradingHom (MvPolynomialHomogenize.MvPolynomial.homogenizedIdeal g d))
            (X none : MvPolynomial (Option σ) R))) r := by
  rw [homogenizedChartRingEquiv_mk, optionChartRingEquiv_symm_C, SpaceChart.MvPolynomial.awayConst, Away.map_mk]
  apply val_injective
  rw [Away.val_mk]
  rfl

/-- The affine-chart identification as an equivalence of coefficient-ring algebras. -/
noncomputable def homogenizedChartAlgEquiv
    (g : κ → MvPolynomial σ R) (d : κ → ℕ)
    (hdeg : ∀ j, (g j).totalDegree ≤ d j) :
    (MvPolynomial σ R ⧸ Ideal.span (Set.range g)) ≃ₐ[R]
      Away (GradedQuotient.HomogeneousIdeal.quotientGrading (MvPolynomialHomogenize.MvPolynomial.homogenizedIdeal g d))
        ((GradedQuotient.HomogeneousIdeal.quotientGradingHom (MvPolynomialHomogenize.MvPolynomial.homogenizedIdeal g d))
          (X none : MvPolynomial (Option σ) R)) :=
  AlgEquiv.ofRingEquiv (f := homogenizedChartRingEquiv g d hdeg) fun r => by
    have hconst : algebraMap R (MvPolynomial σ R ⧸ Ideal.span (Set.range g)) r =
        Ideal.Quotient.mk (Ideal.span (Set.range g)) (C r) := by
      simp [IsScalarTower.algebraMap_apply R (MvPolynomial σ R)
        (MvPolynomial σ R ⧸ Ideal.span (Set.range g)), MvPolynomial.algebraMap_eq,
        Ideal.Quotient.algebraMap_eq]
    rw [hconst, homogenizedChartRingEquiv_mk_C]

/-- The original affine presentation as the homogenizing-coordinate chart of its projective
closure. -/
noncomputable def homogenizedChartOpen
    (g : κ → MvPolynomial σ R) (d : κ → ℕ)
    (hdeg : ∀ j, (g j).totalDegree ≤ d j) :
    Spec (.of (MvPolynomial σ R ⧸ Ideal.span (Set.range g))) ⟶
      homogenizedProj g d :=
  Spec.map (homogenizedChartRingEquiv g d hdeg).toCommRingCatIso.inv ≫
    Proj.awayι (GradedQuotient.HomogeneousIdeal.quotientGrading (MvPolynomialHomogenize.MvPolynomial.homogenizedIdeal g d))
      ((GradedQuotient.HomogeneousIdeal.quotientGradingHom (MvPolynomialHomogenize.MvPolynomial.homogenizedIdeal g d))
        (X none : MvPolynomial (Option σ) R))
      (GradedQuotient.HomogeneousIdeal.mk_mem_quotientGrading (MvPolynomialHomogenize.MvPolynomial.homogenizedIdeal g d)
        (SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one R (none : Option σ))) one_pos

/-- The affine chart map into the homogenized projective closure is an open immersion. -/
lemma homogenizedChartOpen_isOpenImmersion
    (g : κ → MvPolynomial σ R) (d : κ → ℕ)
    (hdeg : ∀ j, (g j).totalDegree ≤ d j) :
    IsOpenImmersion (homogenizedChartOpen g d hdeg) := by
  unfold homogenizedChartOpen
  exact @IsOpenImmersion.comp _ _ _ _ _ (by infer_instance)
    (Proj.instIsOpenImmersionAwayι _ _ _ _)

private lemma homogenizedAwayι_comp_homogenizedProjπ
    (g : κ → MvPolynomial σ R) (d : κ → ℕ) :
    Proj.awayι (GradedQuotient.HomogeneousIdeal.quotientGrading (MvPolynomialHomogenize.MvPolynomial.homogenizedIdeal g d))
        ((GradedQuotient.HomogeneousIdeal.quotientGradingHom (MvPolynomialHomogenize.MvPolynomial.homogenizedIdeal g d))
          (X none : MvPolynomial (Option σ) R))
        (by
          rw [GradedQuotient.HomogeneousIdeal.quotientGradingHom_apply]
          exact GradedQuotient.HomogeneousIdeal.mk_mem_quotientGrading (MvPolynomialHomogenize.MvPolynomial.homogenizedIdeal g d)
            (SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one R (none : Option σ))) one_pos ≫
      homogenizedProjπ g d =
    Spec.map (CommRingCat.ofHom
      (algebraMap R
        (Away (GradedQuotient.HomogeneousIdeal.quotientGrading (MvPolynomialHomogenize.MvPolynomial.homogenizedIdeal g d))
          ((GradedQuotient.HomogeneousIdeal.quotientGradingHom (MvPolynomialHomogenize.MvPolynomial.homogenizedIdeal g d))
            (X none : MvPolynomial (Option σ) R))))) := by
  show Proj.awayι _ _ _ _ ≫ Proj.toSpecZero (GradedQuotient.HomogeneousIdeal.quotientGrading (MvPolynomialHomogenize.MvPolynomial.homogenizedIdeal g d)) ≫
    Spec.map (CommRingCat.ofHom (GradedQuotient.HomogeneousIdeal.algebraMapGradeZero (MvPolynomialHomogenize.MvPolynomial.homogenizedIdeal g d))) = _
  rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

/-- The affine chart immersion commutes with the structure morphisms to the coefficient ring. -/
lemma homogenizedChartOpen_comp_homogenizedProjπ
    (g : κ → MvPolynomial σ R) (d : κ → ℕ)
    (hdeg : ∀ j, (g j).totalDegree ≤ d j) :
    homogenizedChartOpen g d hdeg ≫ homogenizedProjπ g d =
      Spec.map (CommRingCat.ofHom
        (algebraMap R (MvPolynomial σ R ⧸ Ideal.span (Set.range g)))) := by
  unfold homogenizedChartOpen
  rw [Category.assoc, homogenizedAwayι_comp_homogenizedProjπ]
  rw [← Spec.map_comp]
  congr 1
  exact congrArg CommRingCat.ofHom
    (homogenizedChartAlgEquiv g d hdeg).symm.toAlgHom.comp_algebraMap

/-- An affine presentation immersed into polynomial `Proj` through its homogenized projective
closure. -/
def homogenizedAffineImmersion
    (g : κ → MvPolynomial σ R) (d : κ → ℕ)
    (hdeg : ∀ j, (g j).totalDegree ≤ d j) :
    Spec (.of (MvPolynomial σ R ⧸ Ideal.span (Set.range g))) ⟶
      Proj (homogeneousSubmodule (Option σ) R) :=
  homogenizedChartOpen g d hdeg ≫ homogenizedProjι g d

/-- The affine map into polynomial `Proj` obtained from the homogenized closure is an
immersion. -/
lemma homogenizedAffineImmersion_isImmersion
    (g : κ → MvPolynomial σ R) (d : κ → ℕ)
    (hdeg : ∀ j, (g j).totalDegree ≤ d j) :
    IsImmersion (homogenizedAffineImmersion g d hdeg) := by
  let : IsOpenImmersion (homogenizedChartOpen g d hdeg) :=
    homogenizedChartOpen_isOpenImmersion g d hdeg
  let : IsClosedImmersion (homogenizedProjι g d) :=
    homogenizedProjι_isClosedImmersion g d
  unfold homogenizedAffineImmersion
  infer_instance

/-- The affine immersion into polynomial `Proj` is a morphism over the coefficient ring. -/
lemma homogenizedAffineImmersion_comp_homogeneousProjπ
    (g : κ → MvPolynomial σ R) (d : κ → ℕ)
    (hdeg : ∀ j, (g j).totalDegree ≤ d j) :
    homogenizedAffineImmersion g d hdeg ≫
        homogeneousProjπ (R := R) (σ := Option σ) =
      Spec.map (CommRingCat.ofHom
        (algebraMap R (MvPolynomial σ R ⧸ Ideal.span (Set.range g)))) := by
  unfold homogenizedAffineImmersion
  rw [Category.assoc, homogenizedProjι_comp_homogeneousProjπ,
    homogenizedChartOpen_comp_homogenizedProjπ]

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial
