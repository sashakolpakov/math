import OAI.AlgebraicGeometry.Foundations.Scheme.DehomogenizationC
import OAI.AlgebraicGeometry.Foundations.Scheme.HomogeneousEvalMap
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.FiniteType

/-! # Projective -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.Projective.Construction.ProjectiveConstruction

noncomputable section

/-! Generic projective-space charts for the proper-model construction in SpreadingOut.
Adapted from the proved complex projective-chart constructions in this development;
all coefficient-ring arguments are explicit and may be arithmetic rings. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K : Type u} [CommRing K]

/-!
# Standard complex projective space

The scheme is literally the projective spectrum of the polynomial ring with
its standard grading. Its structure map uses the proved identification of the
degree-zero ring with the complex numbers.
-/

/-- The base scheme for complex algebraic geometry. -/
abbrev complexBase : Scheme := Spec (.of K)

/-- The standard homogeneous coordinate ring in `n + 1` variables. -/
abbrev homogeneousCoordinateRing (n : ℕ) := MvPolynomial (Fin (n + 1)) K

/-- The usual grading by total degree. -/
abbrev projectiveGrading (n : ℕ) : ℕ → Submodule K (homogeneousCoordinateRing (K := K) n) :=
  MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K

instance projectiveGradedAlgebra (n : ℕ) : GradedAlgebra (projectiveGrading (K := K) n) :=
  MvPolynomial.gradedAlgebra

/-- Complex projective `n`-space as the genuine scheme `Proj K[X₀,...,Xₙ]`. -/
abbrev projectiveSpace (n : ℕ) : Scheme := AlgebraicGeometry.Proj (projectiveGrading (K := K) n)

/-- The degree-zero ring of the homogeneous coordinate ring consists exactly
of the constant complex polynomials. -/
def degreeZeroConstants (n : ℕ) : K ≃+* projectiveGrading (K := K) n 0 where
  toFun z := ⟨MvPolynomial.C z, MvPolynomial.isHomogeneous_C (Fin (n + 1)) z⟩
  invFun p := AddMonoidAlgebra.coeff (p.val) (0)
  left_inv z := MvPolynomial.coeff_zero_C z
  right_inv p := by
    apply Subtype.ext
    have hp : MvPolynomial.IsHomogeneous p.val 0 := p.property
    exact (MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
      ((MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin (n + 1))).mpr hp)).symm
  map_mul' z w := by
    apply Subtype.ext
    exact map_mul MvPolynomial.C z w
  map_add' z w := by
    apply Subtype.ext
    exact map_add MvPolynomial.C z w

@[simp]
theorem degreeZeroConstants_coe (n : ℕ) (z : K) :
    (degreeZeroConstants (K := K) n z : homogeneousCoordinateRing (K := K) n) = MvPolynomial.C z := rfl

@[simp]
theorem degreeZeroConstants_symm_apply (n : ℕ) (p : projectiveGrading (K := K) n 0) :
    (degreeZeroConstants (K := K) n).symm p = AddMonoidAlgebra.coeff (p.val) (0) := rfl

/-- The standard structure morphism `ℙⁿ_K → Spec K`. -/
def projectiveSpaceToBase (n : ℕ) : projectiveSpace (K := K) n ⟶ complexBase (K := K) :=
  Proj.toSpecZero (projectiveGrading (K := K) n) ≫
    Spec.map (CommRingCat.ofHom (degreeZeroConstants (K := K) n).toRingHom)

/-- On every standard homogeneous chart, the structure morphism is induced
by constants followed by the canonical map to the degree-zero localization. -/
theorem projectiveSpaceToBase_chart (n : ℕ) (m : ℕ)
    (f : homogeneousCoordinateRing (K := K) n) (hf : f ∈ projectiveGrading (K := K) n m) (hm : 0 < m) :
    Proj.awayι (projectiveGrading (K := K) n) f hf hm ≫ projectiveSpaceToBase (K := K) n =
      Spec.map (CommRingCat.ofHom
        ((HomogeneousLocalization.fromZeroRingHom (projectiveGrading (K := K) n) (Submonoid.powers f)).comp
          (degreeZeroConstants (K := K) n).toRingHom)) := by
  rw [projectiveSpaceToBase, ← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

/-!
# The actual standard Proj chart maps to its polynomial coordinate ring

This uses the homogeneous localization that occurs in mathlib's affine chart
isomorphism for `Proj`, rather than a separate model of projective points.
-/

open _root_.MvPolynomial _root_.HomogeneousLocalization
open OAI.AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization

/-- The homogeneous localization defining the standard `i`-th Proj chart. -/
abbrev projectiveChartRing (n : ℕ) (i : Fin (n + 1)) :=
  HomogeneousLocalization.Away (projectiveGrading (K := K) n) (MvPolynomial.X i)

/-- The affine polynomial coordinate ring, omitting the `i`-th variable. -/
abbrev projectiveChartPolynomial (n : ℕ) (i : Fin (n + 1)) :=
  MvPolynomial {j : Fin (n + 1) // j ≠ i} K

theorem projectiveVariable_homogeneous (n : ℕ) (i : Fin (n + 1)) :
    MvPolynomial.X i ∈ projectiveGrading (K := K) n 1 :=
  MvPolynomial.isHomogeneous_X K i

/-- Constant coefficients in the actual homogeneous chart ring. -/
def projectiveChartConstants (n : ℕ) (i : Fin (n + 1)) :
    K →+* projectiveChartRing (K := K) n i :=
  (HomogeneousLocalization.fromZeroRingHom (projectiveGrading (K := K) n)
    (Submonoid.powers (MvPolynomial.X i))).comp (degreeZeroConstants (K := K) n).toRingHom

/-- Setting `Xᵢ = 1` extends to the ordinary localization at `Xᵢ`. -/
def projectiveChartLocalizationToPolynomial (n : ℕ) (i : Fin (n + 1)) :
    Localization.Away (MvPolynomial.X i : homogeneousCoordinateRing (K := K) n) →+*
      projectiveChartPolynomial (K := K) n i :=
  Localization.awayLift (OAI.AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize i) (MvPolynomial.X i)
    (isUnit_iff_exists_inv.mpr ⟨1, by simp⟩)

/-- Dehomogenization restricted to the actual degree-zero localization. -/
def projectiveChartToPolynomial (n : ℕ) (i : Fin (n + 1)) :
    projectiveChartRing (K := K) n i →+* projectiveChartPolynomial (K := K) n i :=
  (projectiveChartLocalizationToPolynomial (K := K) n i).comp
    (algebraMap (projectiveChartRing (K := K) n i)
      (Localization.Away (MvPolynomial.X i : homogeneousCoordinateRing (K := K) n)))

/-- A homogeneous fraction `f / Xᵢ^k` maps exactly to `f(Xᵢ:= 1)`. -/
@[simp]
theorem projectiveChartToPolynomial_mk (n : ℕ) (i : Fin (n + 1))
    (k : ℕ) (f : homogeneousCoordinateRing (K := K) n)
    (hf : f ∈ projectiveGrading (K := K) n (k • (1 : ℕ))) :
    projectiveChartToPolynomial (K := K) n i
      (HomogeneousLocalization.Away.mk (projectiveGrading (K := K) n)
        (projectiveVariable_homogeneous (K := K) n i) k f hf) = OAI.AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize i f := by
  change Localization.awayLift (OAI.AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize i) (MvPolynomial.X i) (by simp)
    (Localization.mk f ⟨MvPolynomial.X i ^ k, k, rfl⟩) = _
  simpa using Localization.awayLift_mk (OAI.AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize i)
    (MvPolynomial.X i) f 1 (by simp) k

/-- Dehomogenization preserves the coefficient homomorphism to the chart. -/
@[simp]
theorem projectiveChartToPolynomial_constants (n : ℕ) (i : Fin (n + 1)) (c : K) :
    projectiveChartToPolynomial (K := K) n i (projectiveChartConstants (K := K) n i c) =
      MvPolynomial.C c := by
  change Localization.awayLift (OAI.AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize i) (MvPolynomial.X i) (by simp)
    (Localization.mk (MvPolynomial.C c) ⟨1, Submonoid.one_mem _⟩) = _
  simpa using Localization.awayLift_mk (OAI.AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize i)
    (MvPolynomial.X i) (MvPolynomial.C c) 1 (by simp) 0

/-!
# Polynomial coordinates are the actual homogeneous localization chart

Variables map to the degree-zero homogeneous fractions `X_j / X_i`. The inverse
identities use homogeneous polynomial evaluation in the ordinary localization,
so this comparison identifies actual rings used by the scheme `Proj`.
-/

/-- A degree-zero coordinate fraction in the actual standard Proj chart. -/
def projectiveChartRatio (n : ℕ) (i j : Fin (n + 1)) : projectiveChartRing (K := K) n i :=
  HomogeneousLocalization.Away.mk (projectiveGrading (K := K) n)
    (projectiveVariable_homogeneous (K := K) n i) 1 (MvPolynomial.X j)
    (by simpa using projectiveVariable_homogeneous (K := K) n j)

@[simp]
theorem projectiveChartToPolynomial_ratio (n : ℕ) (i : Fin (n + 1))
    (j : {j : Fin (n + 1) // j ≠ i}) :
    projectiveChartToPolynomial (K := K) n i (projectiveChartRatio (K := K) n i j.val) = X j := by
  simp [projectiveChartRatio, j.property]

/-- Map an affine polynomial into the homogeneous chart by coordinate ratios. -/
def polynomialToProjectiveChart (n : ℕ) (i : Fin (n + 1)) :
    projectiveChartPolynomial (K := K) n i →+* projectiveChartRing (K := K) n i :=
  MvPolynomial.eval₂Hom (projectiveChartConstants (K := K) n i)
    (fun j => projectiveChartRatio (K := K) n i j.val)

@[simp]
theorem polynomialToProjectiveChart_C (n : ℕ) (i : Fin (n + 1)) (c : K) :
    polynomialToProjectiveChart (K := K) n i (C c) = projectiveChartConstants (K := K) n i c := by
  simp [polynomialToProjectiveChart]

@[simp]
theorem polynomialToProjectiveChart_X (n : ℕ) (i : Fin (n + 1))
    (j : {j : Fin (n + 1) // j ≠ i}) :
    polynomialToProjectiveChart (K := K) n i (X j) = projectiveChartRatio (K := K) n i j.val := by
  simp [polynomialToProjectiveChart]

/-- Substitution back to affine polynomials is a left inverse. -/
theorem projectiveChartToPolynomial_comp (n : ℕ) (i : Fin (n + 1)) :
    (projectiveChartToPolynomial (K := K) n i).comp (polynomialToProjectiveChart (K := K) n i) =
      RingHom.id (projectiveChartPolynomial (K := K) n i) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp
  · intro j
    simp

/-- The constants in the homogeneous chart have their expected value in the
ordinary localization. -/
@[simp]
theorem projectiveChartConstants_val (n : ℕ) (i : Fin (n + 1)) (c : K) :
    (projectiveChartConstants (K := K) n i c).val =
      algebraMap (homogeneousCoordinateRing (K := K) n)
        (Localization.Away (MvPolynomial.X i : homogeneousCoordinateRing (K := K) n)) (C c) := by
  change Localization.mk (C c) 1 = _
  exact Localization.mk_one_eq_algebraMap _

/-- Coordinate fractions have their expected value in the ordinary localization. -/
theorem projectiveChartRatio_val (n : ℕ) (i j : Fin (n + 1)) :
    (projectiveChartRatio (K := K) n i j).val =
      algebraMap (homogeneousCoordinateRing (K := K) n)
        (Localization.Away (MvPolynomial.X i : homogeneousCoordinateRing (K := K) n)) (X j) *
      IsLocalization.Away.invSelf (MvPolynomial.X i : homogeneousCoordinateRing (K := K) n) := by
  simp only [projectiveChartRatio, HomogeneousLocalization.Away.val_mk, pow_one]
  rw [Localization.mk_eq_mk', IsLocalization.mk'_eq_mul_mk'_one]
  rfl

/-- General homogeneous chart fractions have the expected inverse-power denominator. -/
theorem projectiveChartFraction_val (n : ℕ) (i : Fin (n + 1)) (k : ℕ)
    (f : homogeneousCoordinateRing (K := K) n) (hf : f ∈ projectiveGrading (K := K) n (k • (1 : ℕ))) :
    (HomogeneousLocalization.Away.mk (projectiveGrading (K := K) n)
      (projectiveVariable_homogeneous (K := K) n i) k f hf).val =
      IsLocalization.Away.invSelf (S := Localization.Away
        (MvPolynomial.X i : homogeneousCoordinateRing (K := K) n))
        (MvPolynomial.X i : homogeneousCoordinateRing (K := K) n) ^ k *
      algebraMap (homogeneousCoordinateRing (K := K) n)
        (Localization.Away (MvPolynomial.X i : homogeneousCoordinateRing (K := K) n)) f := by
  rw [HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk',
    IsLocalization.mk'_eq_mul_mk'_one, mul_comm]
  congr 1
  simpa only [one_pow, SubmonoidClass.mk_pow, IsLocalization.Away.invSelf] using
    (IsLocalization.mk'_pow
      (S := Localization.Away (MvPolynomial.X i : homogeneousCoordinateRing (K := K) n))
      (1 : homogeneousCoordinateRing (K := K) n)
      (⟨MvPolynomial.X i, Submonoid.mem_powers _⟩ :
        Submonoid.powers (MvPolynomial.X i : homogeneousCoordinateRing (K := K) n)) k)

/-- Substitution by ratios in the ordinary localization is normalization of
all homogeneous variables by the same inverse of `X_i`. -/
theorem projectiveChart_normalization_map (n : ℕ) (i : Fin (n + 1)) :
    ((algebraMap (projectiveChartRing (K := K) n i)
      (Localization.Away (MvPolynomial.X i : homogeneousCoordinateRing (K := K) n))).comp
      (polynomialToProjectiveChart (K := K) n i)).comp (OAI.AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize i) =
    MvPolynomial.eval₂Hom
      ((algebraMap (homogeneousCoordinateRing (K := K) n)
        (Localization.Away (MvPolynomial.X i : homogeneousCoordinateRing (K := K) n))).comp C)
      (fun j => IsLocalization.Away.invSelf
        (MvPolynomial.X i : homogeneousCoordinateRing (K := K) n) *
        algebraMap (homogeneousCoordinateRing (K := K) n)
          (Localization.Away (MvPolynomial.X i : homogeneousCoordinateRing (K := K) n)) (X j)) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp
  · intro j
    by_cases hj : j = i
    · subst j
      simp only [RingHom.comp_apply, OAI.AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize_X_self, map_one, eval₂Hom_X']
      rw [mul_comm, IsLocalization.Away.mul_invSelf]
    · simp [hj, projectiveChartRatio_val (K := K), mul_comm]

/-- Evaluation of all original variables through their localization images
is the localization homomorphism itself. -/
theorem projectiveChart_unnormalized_map (n : ℕ) (i : Fin (n + 1)) :
    MvPolynomial.eval₂Hom
      ((algebraMap (homogeneousCoordinateRing (K := K) n)
        (Localization.Away (MvPolynomial.X i : homogeneousCoordinateRing (K := K) n))).comp C)
      (fun j => algebraMap (homogeneousCoordinateRing (K := K) n)
        (Localization.Away (MvPolynomial.X i : homogeneousCoordinateRing (K := K) n)) (X j)) =
    algebraMap (homogeneousCoordinateRing (K := K) n)
      (Localization.Away (MvPolynomial.X i : homogeneousCoordinateRing (K := K) n)) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp
  · intro j
    simp

/-- Every homogeneous chart fraction is the polynomial in coordinate ratios
obtained by dehomogenizing its numerator. -/
theorem polynomialToProjectiveChart_dehomogenize (n : ℕ) (i : Fin (n + 1)) (k : ℕ)
    (f : homogeneousCoordinateRing (K := K) n) (hf : f ∈ projectiveGrading (K := K) n (k • (1 : ℕ))) :
    polynomialToProjectiveChart (K := K) n i (OAI.AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize i f) =
      HomogeneousLocalization.Away.mk (projectiveGrading (K := K) n)
        (projectiveVariable_homogeneous (K := K) n i) k f hf := by
  apply HomogeneousLocalization.val_injective (Submonoid.powers (MvPolynomial.X i))
  change (((algebraMap (projectiveChartRing (K := K) n i)
      (Localization.Away (MvPolynomial.X i : homogeneousCoordinateRing (K := K) n))).comp
      (polynomialToProjectiveChart (K := K) n i)).comp (OAI.AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize i)) f = _
  rw [projectiveChart_normalization_map (K := K), projectiveChartFraction_val (K := K)]
  have hhom : f.IsHomogeneous k := by simpa using hf
  rw [MvPolynomial.coe_eval₂Hom, OAI.AlgebraicGeometry.Foundations.Scheme.HomogeneousEvalMap.eval₂_mul_of_isHomogeneous hhom]
  congr 1
  exact RingHom.congr_fun (projectiveChart_unnormalized_map (K := K) n i) f

/-- Dehomogenization is also a right inverse on every actual chart fraction. -/
theorem polynomialToProjectiveChart_comp (n : ℕ) (i : Fin (n + 1)) :
    (polynomialToProjectiveChart (K := K) n i).comp (projectiveChartToPolynomial (K := K) n i) =
      RingHom.id (projectiveChartRing (K := K) n i) := by
  apply RingHom.ext
  intro x
  obtain ⟨k, f, hf, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (projectiveGrading (K := K) n) (projectiveVariable_homogeneous (K := K) n i) x
  simpa only [RingHom.comp_apply, RingHom.id_apply, projectiveChartToPolynomial_mk (K := K)] using
    polynomialToProjectiveChart_dehomogenize (K := K) n i k f hf

/-- The standard scheme chart ring is canonically the polynomial ring in all
homogeneous coordinate ratios except the normalized coordinate. -/
def projectiveChartRingEquiv (n : ℕ) (i : Fin (n + 1)) :
    projectiveChartRing (K := K) n i ≃+* projectiveChartPolynomial (K := K) n i where
  toFun := projectiveChartToPolynomial (K := K) n i
  invFun := polynomialToProjectiveChart (K := K) n i
  left_inv x := RingHom.congr_fun (polynomialToProjectiveChart_comp (K := K) n i) x
  right_inv x := RingHom.congr_fun (projectiveChartToPolynomial_comp (K := K) n i) x
  map_add' := map_add (projectiveChartToPolynomial (K := K) n i)
  map_mul' := map_mul (projectiveChartToPolynomial (K := K) n i)

@[simp]
theorem projectiveChartRingEquiv_apply (n : ℕ) (i : Fin (n + 1))
    (x : projectiveChartRing (K := K) n i) :
    projectiveChartRingEquiv (K := K) n i x = projectiveChartToPolynomial (K := K) n i x := rfl

@[simp]
theorem projectiveChartRingEquiv_symm_apply (n : ℕ) (i : Fin (n + 1))
    (p : projectiveChartPolynomial (K := K) n i) :
    (projectiveChartRingEquiv (K := K) n i).symm p = polynomialToProjectiveChart (K := K) n i p := rfl

/-!
# The finite coordinate affine cover of the actual projective scheme

The variables generate the irrelevant ideal of the standard polynomial grading.
Consequently the usual coordinate basic opens cover `Proj K[X₀,...,Xₙ]`.
This file concerns the genuine scheme, not its as-yet separately constructed
ordinary complex topology.
-/

/-- Every positive-degree homogeneous polynomial lies in the ideal of variables. -/
theorem positive_homogeneous_mem_coordinateIdeal (n d : ℕ) (hd : 0 < d)
    (f : homogeneousCoordinateRing (K := K) n) (hf : f ∈ projectiveGrading (K := K) n d) :
    f ∈ Ideal.span (Set.range (MvPolynomial.X : Fin (n + 1) → homogeneousCoordinateRing (K := K) n)) := by
  have hpow : f ∈ MvPolynomial.idealOfVars (Fin (n + 1)) K ^ 1 := by
    rw [MvPolynomial.mem_pow_idealOfVars_iff]
    intro m hm
    have hdeg : m.degree = d := by
      simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using
        hf (MvPolynomial.mem_support_iff.mp hm)
    simpa only [hdeg] using (Nat.succ_le_iff.mpr hd)
  simpa only [pow_one] using hpow

/-- The irrelevant ideal in the standard polynomial grading is generated by the variables. -/
theorem projective_irrelevant_eq_coordinateIdeal (n : ℕ) :
    (HomogeneousIdeal.irrelevant (projectiveGrading (K := K) n)).toIdeal =
      Ideal.span (Set.range (MvPolynomial.X : Fin (n + 1) → homogeneousCoordinateRing (K := K) n)) := by
  apply le_antisymm
  · apply (HomogeneousIdeal.toIdeal_irrelevant_le (projectiveGrading (K := K) n)).mpr
    intro d hd f hf
    exact positive_homogeneous_mem_coordinateIdeal (K := K) n d hd f hf
  · rw [Ideal.span_le]
    rintro f ⟨i, rfl⟩
    exact HomogeneousIdeal.mem_irrelevant_of_mem (projectiveGrading (K := K) n) (by decide : 0 < 1)
      (MvPolynomial.isHomogeneous_X K i)

/-- The usual coordinate open `Xᵢ ≠ 0` inside the genuine projective scheme. -/
abbrev projectiveCoordinateOpen (n : ℕ) (i : Fin (n + 1)) : (projectiveSpace (K := K) n).Opens :=
  Proj.basicOpen (projectiveGrading (K := K) n) (MvPolynomial.X i)

@[simp]
theorem mem_projectiveCoordinateOpen (n : ℕ) (i : Fin (n + 1)) (x : projectiveSpace (K := K) n) :
    x ∈ projectiveCoordinateOpen (K := K) n i ↔ MvPolynomial.X i ∉ x.asHomogeneousIdeal :=
  Proj.mem_basicOpen (projectiveGrading (K := K) n) (MvPolynomial.X i) x

/-- Coordinate opens cover the projective scheme. -/
theorem iSup_projectiveCoordinateOpen (n : ℕ) :
    (⨆ i, projectiveCoordinateOpen (K := K) n i) = ⊤ := by
  apply Proj.iSup_basicOpen_eq_top
  exact (projective_irrelevant_eq_coordinateIdeal (K := K) n).le

/-- In particular, every scheme point belongs to at least one coordinate chart. -/
theorem exists_mem_projectiveCoordinateOpen (n : ℕ) (x : projectiveSpace (K := K) n) :
    ∃ i, x ∈ projectiveCoordinateOpen (K := K) n i := by
  apply TopologicalSpace.Opens.mem_iSup.mp
  rw [iSup_projectiveCoordinateOpen (K := K)]
  trivial

/-- The finite standard affine open cover, with chart rings the actual degree-zero localizations. -/
def projectiveCoordinateAffineCover (n : ℕ) : (projectiveSpace (K := K) n).AffineOpenCover :=
  Proj.affineOpenCoverOfIrrelevantLESpan (projectiveGrading (K := K) n)
    (fun (i : Fin (n + 1)) => MvPolynomial.X i)
    (m := fun _ => 1)
    (fun i => MvPolynomial.isHomogeneous_X K i)
    (fun _ => by decide)
    (projective_irrelevant_eq_coordinateIdeal (K := K) n).le

/-- Its indexing type has precisely the `n + 1` standard coordinates. -/
@[simp]
theorem projectiveCoordinateAffineCover_index (n : ℕ) :
    (projectiveCoordinateAffineCover (K := K) n).I₀ = Fin (n + 1) := rfl

/-- Each coordinate basic open is affine. -/
theorem projectiveCoordinateOpen_isAffine (n : ℕ) (i : Fin (n + 1)) :
    IsAffineOpen (projectiveCoordinateOpen (K := K) n i) :=
  Proj.isAffineOpen_basicOpen (projectiveGrading (K := K) n) (MvPolynomial.X i)
    (MvPolynomial.isHomogeneous_X K i) (by decide : 0 < 1)

/-!
# Standard coordinate charts of the actual projective scheme

The coordinate basic open of `Proj K[X₀,...,Xₙ]` is identified with the spectrum
of the polynomial ring in the remaining `n` coordinates, and hence with
mathlib's actual affine-space scheme. The isomorphisms commute with the given
morphisms to `Spec K`.
-/

/-- The coefficient-field structure map on the polynomial affine chart. -/
abbrev projectiveChartPolynomialToBase (n : ℕ) (i : Fin (n + 1)) :
    Spec (.of (projectiveChartPolynomial (K := K) n i)) ⟶ complexBase (K := K) :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.C : K →+* projectiveChartPolynomial (K := K) n i))

@[simp]
theorem projectiveChartRingEquiv_coe (n : ℕ) (i : Fin (n + 1)) :
    (projectiveChartRingEquiv (K := K) n i : projectiveChartRing (K := K) n i →+* projectiveChartPolynomial (K := K) n i) =
      projectiveChartToPolynomial (K := K) n i := by
  ext x
  rfl

/-- The genuine coordinate basic open is the affine spectrum of its polynomial
coordinate ring, by the proved homogeneous-localization ring equivalence. -/
def projectiveCoordinateIsoSpec (n : ℕ) (i : Fin (n + 1)) :
    (projectiveCoordinateOpen (K := K) n i).toScheme ≅ Spec (.of (projectiveChartPolynomial (K := K) n i)) :=
  Proj.basicOpenIsoSpec (projectiveGrading (K := K) n) (MvPolynomial.X i)
      (projectiveVariable_homogeneous (K := K) n i) (by decide : 0 < 1) ≪≫
    Scheme.Spec.mapIso (projectiveChartRingEquiv (K := K) n i).symm.toCommRingCatIso.op

/-- On the inverse chart map, the scheme morphism is induced by the explicit
ring homomorphism sending homogeneous fractions to dehomogenized polynomials. -/
@[reassoc]
theorem projectiveCoordinateIsoSpec_inv_ι (n : ℕ) (i : Fin (n + 1)) :
    (projectiveCoordinateIsoSpec (K := K) n i).inv ≫ (projectiveCoordinateOpen (K := K) n i).ι =
      Spec.map (CommRingCat.ofHom (projectiveChartToPolynomial (K := K) n i)) ≫
        Proj.awayι (projectiveGrading (K := K) n) (MvPolynomial.X i)
          (projectiveVariable_homogeneous (K := K) n i) (by decide : 0 < 1) := by
  simp [projectiveCoordinateIsoSpec, Proj.awayι, Category.assoc]

/-- The inverse chart identification is a morphism over the complex base. -/
@[reassoc]
theorem projectiveCoordinateIsoSpec_inv_over (n : ℕ) (i : Fin (n + 1)) :
    (projectiveCoordinateIsoSpec (K := K) n i).inv ≫ (projectiveCoordinateOpen (K := K) n i).ι ≫
      projectiveSpaceToBase (K := K) n = projectiveChartPolynomialToBase (K := K) n i := by
  rw [projectiveCoordinateIsoSpec_inv_ι_assoc, projectiveSpaceToBase_chart (K := K)]
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact projectiveChartToPolynomial_constants (K := K) n i c

/-- The chart isomorphism respects the actual structure morphisms to `Spec K`. -/
@[reassoc]
theorem projectiveCoordinateIsoSpec_over (n : ℕ) (i : Fin (n + 1)) :
    (projectiveCoordinateIsoSpec (K := K) n i).hom ≫ projectiveChartPolynomialToBase (K := K) n i =
      (projectiveCoordinateOpen (K := K) n i).ι ≫ projectiveSpaceToBase (K := K) n := by
  apply (cancel_epi (projectiveCoordinateIsoSpec (K := K) n i).inv).mp
  simpa only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] using
    (projectiveCoordinateIsoSpec_inv_over (K := K) n i).symm

/-- The same chart comparison as an isomorphism in the category over `Spec K`. -/
def projectiveCoordinateOverIso (n : ℕ) (i : Fin (n + 1)) :
    Over.mk ((projectiveCoordinateOpen (K := K) n i).ι ≫ projectiveSpaceToBase (K := K) n) ≅
      Over.mk (projectiveChartPolynomialToBase (K := K) n i) :=
  Over.isoMk (projectiveCoordinateIsoSpec (K := K) n i) (projectiveCoordinateIsoSpec_over (K := K) n i)

/-- The standard polynomial affine chart map into projective space. -/
def projectiveAffineChartMap (n : ℕ) (i : Fin (n + 1)) :
    Spec (.of (projectiveChartPolynomial (K := K) n i)) ⟶ projectiveSpace (K := K) n :=
  (projectiveCoordinateIsoSpec (K := K) n i).inv ≫ (projectiveCoordinateOpen (K := K) n i).ι

instance (n : ℕ) (i : Fin (n + 1)) : IsOpenImmersion (projectiveAffineChartMap (K := K) n i) := by
  dsimp [projectiveAffineChartMap]
  infer_instance

@[reassoc]
theorem projectiveAffineChartMap_over (n : ℕ) (i : Fin (n + 1)) :
    projectiveAffineChartMap (K := K) n i ≫ projectiveSpaceToBase (K := K) n =
      projectiveChartPolynomialToBase (K := K) n i := by
  exact projectiveCoordinateIsoSpec_inv_over (K := K) n i

/-- The omitted-coordinate index has exactly `n` elements. -/
theorem projectiveChartCoordinate_card (n : ℕ) (i : Fin (n + 1)) :
    Fintype.card {j : Fin (n + 1) // j ≠ i} = n := by
  rw [Fintype.card_subtype_compl (fun j : Fin (n + 1) => j = i)]
  simp

/-! Finite generation of the homogeneous coordinate ring over its degree-zero ring. -/

/-- The polynomial coordinate ring is finitely generated as an algebra over
its actual degree-zero coefficient ring. -/
instance homogeneousCoordinateRing_finiteType_over_zero (n : ℕ) :
    Algebra.FiniteType (projectiveGrading (K := K) n 0) (homogeneousCoordinateRing (K := K) n) := by
  let : IsScalarTower K (projectiveGrading (K := K) n 0) (homogeneousCoordinateRing (K := K) n) :=
    IsScalarTower.of_algebraMap_eq
      (R := K) (S := projectiveGrading (K := K) n 0) (A := homogeneousCoordinateRing (K := K) n)
      (fun _ => rfl)
  exact Algebra.FiniteType.of_restrictScalars_finiteType
    K (projectiveGrading (K := K) n 0) (homogeneousCoordinateRing (K := K) n)

instance projectiveSpace_proper (n : ℕ) : IsProper (projectiveSpaceToBase (K := K) n) := by
  have : IsIso (Spec.map (CommRingCat.ofHom (degreeZeroConstants (K := K) n).toRingHom)) :=
    inferInstanceAs (IsIso (Scheme.Spec.mapIso (degreeZeroConstants (K := K) n).toCommRingCatIso.op).hom)
  have hp : IsProper (Proj.toSpecZero (projectiveGrading (K := K) n)) := inferInstance
  have he : IsProper (Spec.map (CommRingCat.ofHom (degreeZeroConstants (K := K) n).toRingHom)) := inferInstance
  change IsProper (Proj.toSpecZero (projectiveGrading (K := K) n) ≫
    Spec.map (CommRingCat.ofHom (degreeZeroConstants (K := K) n).toRingHom))
  exact IsProper.stableUnderComposition.comp_mem _ _ hp he

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.Projective.Construction.ProjectiveConstruction
