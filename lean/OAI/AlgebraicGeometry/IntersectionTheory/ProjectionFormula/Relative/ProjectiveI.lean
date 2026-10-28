import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.ProjectiveLinear
import Mathlib.RingTheory.MvPolynomial.Ideal

/-! # Projective I -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.ProjectiveI

noncomputable section

section

/-! Coefficient specialization induces an actual relative projective
map and commutes with invertible matrix actions. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace Scalars

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.ProjectiveLinear

variable {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ)

def graded : ProjectiveLinear.grading R n →+*ᵍ ProjectiveLinear.grading S n where
  __ := MvPolynomial.map f
  map_mem hp := hp.map f

theorem irrelevant_le : HomogeneousIdeal.irrelevant (ProjectiveLinear.grading S n) ≤
    (HomogeneousIdeal.irrelevant (ProjectiveLinear.grading R n)).map (graded f n) := by
  apply (HomogeneousIdeal.irrelevant_le (ProjectiveLinear.grading S n)).mpr
  intro d hd p hp
  have hv : p ∈ Ideal.span (Set.range (MvPolynomial.X : Fin (n + 1) → MvPolynomial (Fin (n + 1)) S)) := by
    rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
    intro a ha
    by_contra hn
    push Not at hn
    have hz : a = 0 := Finsupp.ext (fun i => hn i (Set.mem_univ i))
    have hh := hp (MvPolynomial.mem_support_iff.mp ha)
    rw [hz, map_zero] at hh
    omega
  apply (Ideal.span_le.mpr ?_) hv
  rintro _ ⟨i, rfl⟩
  have hi : MvPolynomial.X i ∈ HomogeneousIdeal.irrelevant (ProjectiveLinear.grading R n) :=
    HomogeneousIdeal.mem_irrelevant_of_mem _ Nat.zero_lt_one (MvPolynomial.isHomogeneous_X R i)
  have hm := Ideal.mem_map_of_mem (graded f n).toRingHom hi
  change MvPolynomial.map f (MvPolynomial.X i) ∈
    ((HomogeneousIdeal.irrelevant (ProjectiveLinear.grading R n)).map (graded f n)).toIdeal at hm
  rw [MvPolynomial.map_X] at hm
  exact hm

def map : ProjectiveLinear.space S n ⟶ ProjectiveLinear.space R n := Proj.map (graded f n) (Scalars.irrelevant_le f n)

theorem map_form (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (i : Fin (n + 1)) :
    MvPolynomial.map f (ProjectiveLinear.form A i) = ProjectiveLinear.form (f.mapMatrix A) i := by
  simp [ProjectiveLinear.form]

theorem graded_naturality (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    (graded f n).comp (ProjectiveLinear.gradedHom A) = (ProjectiveLinear.gradedHom (f.mapMatrix A)).comp (graded f n) := by
  have h : (MvPolynomial.map f).comp (ProjectiveLinear.algebraHom A).toRingHom =
      (ProjectiveLinear.algebraHom (f.mapMatrix A)).toRingHom.comp (MvPolynomial.map f) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        ProjectiveLinear.algebraHom_C, MvPolynomial.map_C]
    · intro i
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        ProjectiveLinear.algebraHom_X, MvPolynomial.map_X]
      exact map_form f n A i
  apply GradedRingHom.ext
  intro p
  exact DFunLike.congr_fun h p

def unit (A : (Matrix (Fin (n + 1)) (Fin (n + 1)) R)ˣ) :
    (Matrix (Fin (n + 1)) (Fin (n + 1)) S)ˣ := Units.map (f.mapMatrix.toMonoidHom) A

theorem naturality (A : (Matrix (Fin (n + 1)) (Fin (n + 1)) R)ˣ) :
    ProjectiveLinear.map (unit f n A) ≫ Scalars.map f n =
      Scalars.map f n ≫ ProjectiveLinear.map A := by
  unfold Scalars.map ProjectiveLinear.map
  rw [← Proj.map_comp, ← Proj.map_comp]
  congr 1
  exact (graded_naturality f n A.val).symm

end Scalars

end

section

/-! Relative projective coordinate changes preserve the coefficient
scheme, and coefficient specialization gives a commutative base square. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.HomogeneousLocalization

namespace Base

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.ProjectiveLinear

def constants (R : Type) [CommRing R] (n : ℕ) : R ≃+* ProjectiveLinear.grading R n 0 where
  toFun r := ⟨MvPolynomial.C r, MvPolynomial.isHomogeneous_C (Fin (n + 1)) r⟩
  invFun p := AddMonoidAlgebra.coeff (p.val) (0)
  left_inv r := MvPolynomial.coeff_zero_C r
  right_inv p := by
    apply Subtype.ext
    exact (MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
      ((MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin (n + 1))).mpr p.property)).symm
  map_mul' r s := by apply Subtype.ext; exact map_mul MvPolynomial.C r s
  map_add' r s := by apply Subtype.ext; exact map_add MvPolynomial.C r s

def base (R : Type) [CommRing R] (n : ℕ) : ProjectiveLinear.space R n ⟶ Spec (.of R) :=
  Proj.toSpecZero (ProjectiveLinear.grading R n) ≫ Spec.map (CommRingCat.ofHom (constants R n).toRingHom)

variable {R S : Type} [CommRing R] [CommRing S] {m n : ℕ}

theorem away_zero (f : ProjectiveLinear.grading R m →+*ᵍ ProjectiveLinear.grading S n)
    (s : MvPolynomial (Fin (m + 1)) R) (a : ProjectiveLinear.grading R m 0) :
    Away.map f s (fromZeroRingHom (ProjectiveLinear.grading R m) (Submonoid.powers s) a) =
      fromZeroRingHom (ProjectiveLinear.grading S n) (Submonoid.powers (f s)) (f.gradedZeroRingHom a) := by
  change HomogeneousLocalization.map f _ (HomogeneousLocalization.mk ⟨0, a, 1, by simp⟩) =
    HomogeneousLocalization.mk ⟨0, f.gradedZeroRingHom a, 1, by simp⟩
  rw [HomogeneousLocalization.map_mk]
  congr 1
  apply HomogeneousLocalization.NumDenSameDeg.ext
  · rfl
  · rfl
  · exact map_one f

theorem to_zero (f : ProjectiveLinear.grading R m →+*ᵍ ProjectiveLinear.grading S n)
    (hf : HomogeneousIdeal.irrelevant (ProjectiveLinear.grading S n) ≤ (HomogeneousIdeal.irrelevant (ProjectiveLinear.grading R m)).map f) :
    Proj.map f hf ≫ Proj.toSpecZero (ProjectiveLinear.grading R m) =
      Proj.toSpecZero (ProjectiveLinear.grading S n) ≫ Spec.map (CommRingCat.ofHom f.gradedZeroRingHom) := by
  apply (Proj.mapAffineOpenCover f hf).openCover.hom_ext
  intro s
  change Proj.awayι (ProjectiveLinear.grading S n) (f s.2) (f.map_mem s.2.2) s.1.2 ≫
      (Proj.map f hf ≫ Proj.toSpecZero (ProjectiveLinear.grading R m)) =
    Proj.awayι (ProjectiveLinear.grading S n) (f s.2) (f.map_mem s.2.2) s.1.2 ≫
      (Proj.toSpecZero (ProjectiveLinear.grading S n) ≫ Spec.map (CommRingCat.ofHom f.gradedZeroRingHom))
  rw [← Category.assoc, Proj.awayι_comp_map f hf s.1.2 s.2 s.2.2, Category.assoc,
    Proj.awayι_toSpecZero, ← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext r
  exact congrArg HomogeneousLocalization.val (away_zero f s.2 r)

theorem over (f : ProjectiveLinear.grading R m →+*ᵍ ProjectiveLinear.grading S n)
    (hf : HomogeneousIdeal.irrelevant (ProjectiveLinear.grading S n) ≤ (HomogeneousIdeal.irrelevant (ProjectiveLinear.grading R m)).map f)
    (g : R →+* S) (hg : ∀ r, f (MvPolynomial.C r) = MvPolynomial.C (g r)) :
    Proj.map f hf ≫ base R m = base S n ≫ Spec.map (CommRingCat.ofHom g) := by
  have hz : f.gradedZeroRingHom.comp (constants R m).toRingHom =
      (constants S n).toRingHom.comp g := by
    apply RingHom.ext
    intro r
    apply Subtype.ext
    exact hg r
  rw [base, ← Category.assoc, to_zero f hf, Category.assoc, ← Spec.map_comp]
  change Proj.toSpecZero (ProjectiveLinear.grading S n) ≫ Spec.map (CommRingCat.ofHom
    (f.gradedZeroRingHom.comp (constants R m).toRingHom)) = _
  rw [hz]
  change Proj.toSpecZero (ProjectiveLinear.grading S n) ≫ Spec.map
    (CommRingCat.ofHom g ≫ CommRingCat.ofHom (constants S n).toRingHom) = _
  rw [Spec.map_comp]
  rfl

theorem matrix_over (A : (Matrix (Fin (n + 1)) (Fin (n + 1)) R)ˣ) :
    ProjectiveLinear.map A ≫ base R n = base R n := by
  have h := over (ProjectiveLinear.gradedHom A.val) (ProjectiveLinear.irrelevant_le A) (RingHom.id R)
    (fun r => ProjectiveLinear.algebraHom_C A.val r)
  change ProjectiveLinear.map A ≫ base R n = base R n ≫ Spec.map (𝟙 (CommRingCat.of R)) at h
  rw [Spec.map_id, Category.comp_id] at h
  exact h

theorem scalar_over (f : R →+* S) (n : ℕ) :
    Scalars.map f n ≫ base R n = base S n ≫ Spec.map (CommRingCat.ofHom f) :=
  over (Scalars.graded f n) (Scalars.irrelevant_le f n) f
    (fun r => MvPolynomial.map_C f r)

end Base

end

/-!
# The finite coordinate affine cover of the actual projective scheme

The variables generate the irrelevant ideal of the standard polynomial grading.
Consequently the usual coordinate basic opens cover `Proj R[X₀,...,Xₙ]`.
This file concerns the genuine scheme, not its as-yet separately constructed
ordinary complex topology.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace Chart

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.ProjectiveLinear (grading space)

/-- Every positive-degree homogeneous polynomial lies in the ideal of variables. -/
theorem positive_homogeneous_mem_coordinateIdeal (R : Type) [CommRing R] (n d : ℕ) (hd : 0 < d)
    (f : MvPolynomial (Fin (n + 1)) R) (hf : f ∈ ProjectiveLinear.grading R n d) :
    f ∈ Ideal.span (Set.range (MvPolynomial.X : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R)) := by
  have hpow : f ∈ MvPolynomial.idealOfVars (Fin (n + 1)) R ^ 1 := by
    rw [MvPolynomial.mem_pow_idealOfVars_iff]
    intro m hm
    have hdeg : m.degree = d := by
      simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using
        hf (MvPolynomial.mem_support_iff.mp hm)
    simpa only [hdeg] using (Nat.succ_le_iff.mpr hd)
  simpa only [pow_one] using hpow

/-- The irrelevant ideal in the standard polynomial grading is generated by the variables. -/
theorem projective_irrelevant_eq_coordinateIdeal (R : Type) [CommRing R] (n : ℕ) :
    (HomogeneousIdeal.irrelevant (ProjectiveLinear.grading R n)).toIdeal =
      Ideal.span (Set.range (MvPolynomial.X : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R)) := by
  apply le_antisymm
  · apply (HomogeneousIdeal.toIdeal_irrelevant_le (ProjectiveLinear.grading R n)).mpr
    intro d hd f hf
    exact positive_homogeneous_mem_coordinateIdeal R n d hd f hf
  · rw [Ideal.span_le]
    rintro f ⟨i, rfl⟩
    exact HomogeneousIdeal.mem_irrelevant_of_mem (ProjectiveLinear.grading R n) (by decide : 0 < 1)
      (MvPolynomial.isHomogeneous_X R i)

/-- The usual coordinate open `Xᵢ ≠ 0` inside the genuine projective scheme. -/
abbrev projectiveCoordinateOpen (R : Type) [CommRing R] (n : ℕ) (i : Fin (n + 1)) : (ProjectiveLinear.space R n).Opens :=
  Proj.basicOpen (ProjectiveLinear.grading R n) (MvPolynomial.X i)

@[simp]
theorem mem_projectiveCoordinateOpen (R : Type) [CommRing R] (n : ℕ) (i : Fin (n + 1)) (x : ProjectiveLinear.space R n) :
    x ∈ projectiveCoordinateOpen R n i ↔ MvPolynomial.X i ∉ x.asHomogeneousIdeal :=
  Proj.mem_basicOpen (ProjectiveLinear.grading R n) (MvPolynomial.X i) x

/-- Coordinate opens cover the projective scheme. -/
theorem iSup_projectiveCoordinateOpen (R : Type) [CommRing R] (n : ℕ) :
    (⨆ i, projectiveCoordinateOpen R n i) = ⊤ := by
  apply Proj.iSup_basicOpen_eq_top
  exact (projective_irrelevant_eq_coordinateIdeal R n).le

/-- In particular, every scheme point belongs to at least one coordinate chart. -/
theorem exists_mem_projectiveCoordinateOpen (R : Type) [CommRing R] (n : ℕ) (x : ProjectiveLinear.space R n) :
    ∃ i, x ∈ projectiveCoordinateOpen R n i := by
  apply TopologicalSpace.Opens.mem_iSup.mp
  rw [iSup_projectiveCoordinateOpen]
  trivial

/-- The finite standard affine open cover, with chart rings the actual degree-zero localizations. -/
def projectiveCoordinateAffineCover (R : Type) [CommRing R] (n : ℕ) : (ProjectiveLinear.space R n).AffineOpenCover :=
  Proj.affineOpenCoverOfIrrelevantLESpan (ProjectiveLinear.grading R n)
    (fun (i : Fin (n + 1)) => MvPolynomial.X i)
    (m := fun _ => 1)
    (fun i => MvPolynomial.isHomogeneous_X R i)
    (fun _ => by decide)
    (projective_irrelevant_eq_coordinateIdeal R n).le

/-- Its indexing type has precisely the `n + 1` standard coordinates. -/
@[simp]
theorem projectiveCoordinateAffineCover_index (R : Type) [CommRing R] (n : ℕ) :
    (projectiveCoordinateAffineCover R n).I₀ = Fin (n + 1) := rfl

/-- Each coordinate basic open is affine. -/
theorem projectiveCoordinateOpen_isAffine (R : Type) [CommRing R] (n : ℕ) (i : Fin (n + 1)) :
    IsAffineOpen (projectiveCoordinateOpen R n i) :=
  Proj.isAffineOpen_basicOpen (ProjectiveLinear.grading R n) (MvPolynomial.X i)
    (MvPolynomial.isHomogeneous_X R i) (by decide : 0 < 1)

end Chart

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.ProjectiveI
