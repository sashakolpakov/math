import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.FamilySections
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.ProjectivePullback
import Mathlib.Algebra.MvPolynomial.Equiv

/-! # Family Is -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.FamilyIs

noncomputable section

section

/-! The marked sections of the projective matrix family are its full
scheme-theoretic parameter fibers. The source model is the actual
base change of the fixed smooth projective source. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.Polynomial

namespace FamilyFibers

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.MatrixPath OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.FamilyOnSource.Family OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.FamilySections.Family

theorem ambient {n : ℕ} (A : (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)ˣ)
    (t : ℂ) (ht : (ProjectionFormula.Polynomial.MatrixPath.determinant A).eval t ≠ 0) :
    IsPullback (MatrixFamily.Family.specialization A t ht) (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)
      (Relative.ProjectiveI.Base.base (ProjectionFormula.Polynomial.MatrixPath.Ring A) n) (Spec.map (CommRingCat.ofHom (ProjectionFormula.Polynomial.MatrixPath.evaluation A t ht))) :=
  Relative.ProjectivePullback.isPullback (ProjectionFormula.Polynomial.MatrixPath.evaluation A t ht) n

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
  (A : (Matrix (Fin (X.ambientDimension + 1)) (Fin (X.ambientDimension + 1)) ℂ)ˣ)

theorem source_base_change :
    IsPullback (FamilyOnSource.Family.toSource X A) (FamilySections.Family.parameter X A) X.structureMap
      (Spec.map (CommRingCat.ofHom (FamilySupport.Family.coefficients A))) := by
  have h := (IsPullback.of_hasPullback (FamilySupport.Family.projection A) X.embedding).paste_horiz
    (Relative.ProjectivePullback.isPullback (FamilySupport.Family.coefficients A) X.ambientDimension).flip
  change IsPullback (FamilySections.Family.parameter X A) (FamilyOnSource.Family.toSource X A)
    (Spec.map (CommRingCat.ofHom (FamilySupport.Family.coefficients A)))
    (X.embedding ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase X.ambientDimension) at h
  rw [X.embedding_over] at h
  exact h.flip

theorem specialization_parameter (t : ℂ) (ht : (ProjectionFormula.Polynomial.MatrixPath.determinant A).eval t ≠ 0) :
    FamilyOnSource.Family.specialization X A t ht ≫ FamilySections.Family.parameter X A =
      X.structureMap ≫ Spec.map (CommRingCat.ofHom (ProjectionFormula.Polynomial.MatrixPath.evaluation A t ht)) := by
  rw [FamilySections.Family.parameter, ← Category.assoc, FamilyOnSource.Family.specialization_ambient, Category.assoc,
    MatrixFamily.Family.specialization_base, ← Category.assoc, X.embedding_over]

theorem scalar_retraction (t : ℂ) (ht : (ProjectionFormula.Polynomial.MatrixPath.determinant A).eval t ≠ 0) :
    Spec.map (CommRingCat.ofHom (ProjectionFormula.Polynomial.MatrixPath.evaluation A t ht)) ≫
      Spec.map (CommRingCat.ofHom (FamilySupport.Family.coefficients A)) = 𝟙 Foundations.Scheme.ProjectiveSpace.complexBase := by
  have he : (ProjectionFormula.Polynomial.MatrixPath.evaluation A t ht).comp (FamilySupport.Family.coefficients A) = RingHom.id ℂ := by
    ext c
    change ProjectionFormula.Polynomial.MatrixPath.evaluation A t ht (algebraMap ℂ[X] (ProjectionFormula.Polynomial.MatrixPath.Ring A) (Polynomial.C c)) = c
    rw [ProjectionFormula.Polynomial.MatrixPath.evaluation_algebraMap, Polynomial.eval_C]
  rw [← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom ((ProjectionFormula.Polynomial.MatrixPath.evaluation A t ht).comp (FamilySupport.Family.coefficients A))) = _
  rw [he]
  exact Spec.map_id _

theorem source (t : ℂ) (ht : (ProjectionFormula.Polynomial.MatrixPath.determinant A).eval t ≠ 0) :
    IsPullback (FamilyOnSource.Family.specialization X A t ht) X.structureMap (FamilySections.Family.parameter X A)
      (Spec.map (CommRingCat.ofHom (ProjectionFormula.Polynomial.MatrixPath.evaluation A t ht))) := by
  apply (IsPullback.paste_horiz_iff (source_base_change X A) (specialization_parameter X A t ht)).mp
  rw [FamilyOnSource.Family.specialization_source, scalar_retraction]
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

end FamilyFibers

end

section

/-! The determinant localization is an actual open subscheme of the
projective parameter line, and every good scalar specialization factors
through its usual affine coordinate. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Polynomial

namespace MatrixParameterOpen

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.MatrixPath

instance chartIndex : Unique {j : Fin (1 + 1) // j ≠ 0} where
  default := ⟨1, by decide⟩
  uniq j := by
    rcases j with ⟨j, hj⟩
    fin_cases j
    · exact (hj rfl).elim
    · rfl

def chartEquiv : Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial 1 0 ≃ₐ[ℂ] ℂ[X] :=
  MvPolynomial.uniqueAlgEquiv ℂ {j : Fin (1 + 1) // j ≠ 0}

def affine : Spec (.of ℂ[X]) ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace 1 :=
  Spec.map (CommRingCat.ofHom chartEquiv.toRingHom) ≫ Foundations.Scheme.ProjectiveChart.projectiveAffineChartMap 1 0

instance affine_open : IsOpenImmersion affine := by
  let : IsIso (Spec.map (CommRingCat.ofHom chartEquiv.toRingHom)) :=
    inferInstanceAs (IsIso (Scheme.Spec.mapIso chartEquiv.toRingEquiv.toCommRingCatIso.op).hom)
  unfold affine
  infer_instance

theorem affine_over : affine ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1 =
    Spec.map (CommRingCat.ofHom (Polynomial.C : ℂ →+* ℂ[X])) := by
  rw [affine, Category.assoc, Foundations.Scheme.ProjectiveChart.projectiveAffineChartMap_over, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact chartEquiv.commutes c

def point (t : ℂ) : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace 1 :=
  Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom t)) ≫ affine

variable {n : ℕ} (A : (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)ˣ)

def inclusion : Spec (.of (ProjectionFormula.Polynomial.MatrixPath.Ring A)) ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace 1 :=
  Spec.map (CommRingCat.ofHom (algebraMap ℂ[X] (ProjectionFormula.Polynomial.MatrixPath.Ring A))) ≫ affine

instance inclusion_open : IsOpenImmersion (inclusion A) := by
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap ℂ[X] (ProjectionFormula.Polynomial.MatrixPath.Ring A)))) :=
    IsOpenImmersion.of_isLocalization (ProjectionFormula.Polynomial.MatrixPath.determinant A)
  unfold inclusion
  infer_instance

theorem over_base : inclusion A ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1 =
    Spec.map (CommRingCat.ofHom (FamilySupport.Family.coefficients A)) := by
  rw [inclusion, Category.assoc, affine_over, ← Spec.map_comp]
  rfl

theorem evaluation (t : ℂ) (ht : (ProjectionFormula.Polynomial.MatrixPath.determinant A).eval t ≠ 0) :
    Spec.map (CommRingCat.ofHom (ProjectionFormula.Polynomial.MatrixPath.evaluation A t ht)) ≫ inclusion A = point t := by
  have he : (ProjectionFormula.Polynomial.MatrixPath.evaluation A t ht).comp (algebraMap ℂ[X] (ProjectionFormula.Polynomial.MatrixPath.Ring A)) = Polynomial.evalRingHom t := by
    apply RingHom.ext
    exact ProjectionFormula.Polynomial.MatrixPath.evaluation_algebraMap A t ht
  rw [inclusion, ← Category.assoc, ← Spec.map_comp]
  exact congrArg (fun f : ℂ[X] →+* ℂ => Spec.map (CommRingCat.ofHom f) ≫ affine) he

end MatrixParameterOpen

end

/-! The moving source model is an open subscheme of the proper
product with the projective parameter line. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

namespace FamilyCompactAmbient

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.MatrixPath OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.FamilyOnSource.Family OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.FamilySections.Family

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)

abbrev space : Scheme := pullback X.structureMap (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1)

def first : space X ⟶ X.carrier := pullback.fst _ _

def second : space X ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace 1 := pullback.snd _ _

instance first_proper : IsProper (first X) :=
  inferInstanceAs (IsProper (pullback.fst X.structureMap (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1)))

instance noetherian : IsNoetherian (space X) where

variable (A : (Matrix (Fin (X.ambientDimension + 1)) (Fin (X.ambientDimension + 1)) ℂ)ˣ)

def inclusion : FamilyOnSource.Family.space X A ⟶ space X :=
  pullback.lift (FamilyOnSource.Family.toSource X A) (FamilySections.Family.parameter X A ≫ MatrixParameterOpen.inclusion A) (by
    rw [Category.assoc, MatrixParameterOpen.over_base]
    exact (FamilyFibers.source_base_change X A).w)

theorem inclusion_first : inclusion X A ≫ first X = FamilyOnSource.Family.toSource X A := pullback.lift_fst _ _ _

theorem inclusion_second : inclusion X A ≫ second X = FamilySections.Family.parameter X A ≫ MatrixParameterOpen.inclusion A :=
  pullback.lift_snd _ _ _

theorem isPullback : IsPullback (inclusion X A) (FamilySections.Family.parameter X A) (second X)
    (MatrixParameterOpen.inclusion A) := by
  apply (IsPullback.paste_horiz_iff (IsPullback.of_hasPullback X.structureMap (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1))
    (inclusion_second X A)).mp
  change IsPullback (inclusion X A ≫ first X) (FamilySections.Family.parameter X A) X.structureMap
    (MatrixParameterOpen.inclusion A ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1)
  rw [inclusion_first, MatrixParameterOpen.over_base]
  exact FamilyFibers.source_base_change X A

instance inclusion_open : IsOpenImmersion (inclusion X A) := by
  let h := isPullback X A
  have hi : IsOpenImmersion (h.isoPullback.hom ≫ pullback.fst (second X) (MatrixParameterOpen.inclusion A)) :=
    inferInstance
  rw [h.isoPullback_hom_fst] at hi
  exact hi

end FamilyCompactAmbient

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.FamilyIs
