import OAI.AlgebraicGeometry.SheafCohomology.Projective.CoordinateBundlePullback
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.ProjectiveI

/-! # Scalar Bundle -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.ScalarBundle

noncomputable section

/-! Coefficient-ring isomorphisms induce actual projective isomorphisms
over the base and preserve the concrete hyperplane line bundle. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial
open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.ProjectiveLinear
attribute [local instance] MvPolynomial.gradedAlgebra

theorem projectiveScalarMap_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (n : ℕ) :
    IntersectionTheory.ProjectionFormula.Relative.ProjectiveI.Scalars.map g n ≫ IntersectionTheory.ProjectionFormula.Relative.ProjectiveI.Scalars.map f n =
      IntersectionTheory.ProjectionFormula.Relative.ProjectiveI.Scalars.map (g.comp f) n := by
  unfold IntersectionTheory.ProjectionFormula.Relative.ProjectiveI.Scalars.map
  rw [← Proj.map_comp]
  congr 1
  apply GradedRingHom.ext
  intro p
  exact MvPolynomial.map_map f g p

theorem projectiveScalarMap_id (R : Type) [CommRing R] (n : ℕ) :
    IntersectionTheory.ProjectionFormula.Relative.ProjectiveI.Scalars.map (RingHom.id R) n = 𝟙 (IntersectionTheory.ProjectionFormula.Relative.ProjectiveLinear.space R n) := by
  have h : IntersectionTheory.ProjectionFormula.Relative.ProjectiveI.Scalars.graded (RingHom.id R) n = GradedRingHom.id (IntersectionTheory.ProjectionFormula.Relative.ProjectiveLinear.grading R n) := by
    apply GradedRingHom.ext
    intro p
    exact MvPolynomial.map_id p
  unfold IntersectionTheory.ProjectionFormula.Relative.ProjectiveI.Scalars.map
  have he : Proj.map (IntersectionTheory.ProjectionFormula.Relative.ProjectiveI.Scalars.graded (RingHom.id R) n)
      (IntersectionTheory.ProjectionFormula.Relative.ProjectiveI.Scalars.irrelevant_le (RingHom.id R) n) =
      Proj.map (GradedRingHom.id (IntersectionTheory.ProjectionFormula.Relative.ProjectiveLinear.grading R n)) (by simp) := by
    congr 1
  exact he.trans Proj.map_id

def projectiveScalarIso {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S) (n : ℕ) :
    IntersectionTheory.ProjectionFormula.Relative.ProjectiveLinear.space S n ≅ IntersectionTheory.ProjectionFormula.Relative.ProjectiveLinear.space R n where
  hom := IntersectionTheory.ProjectionFormula.Relative.ProjectiveI.Scalars.map e.toRingHom n
  inv := IntersectionTheory.ProjectionFormula.Relative.ProjectiveI.Scalars.map e.symm.toRingHom n
  hom_inv_id := by
    rw [projectiveScalarMap_comp]
    have h : e.toRingHom.comp e.symm.toRingHom = RingHom.id S := by
      ext r
      exact e.apply_symm_apply r
    rw [h, projectiveScalarMap_id]
  inv_hom_id := by
    rw [projectiveScalarMap_comp]
    have h : e.symm.toRingHom.comp e.toRingHom = RingHom.id R := by
      ext r
      exact e.symm_apply_apply r
    rw [h, projectiveScalarMap_id]

theorem relativeProjectiveBase_eq (R : Type) [CommRing R] (n : ℕ) :
    IntersectionTheory.ProjectionFormula.Relative.ProjectiveI.Base.base R n =
      MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n + 1)) := by
  unfold IntersectionTheory.ProjectionFormula.Relative.ProjectiveI.Base.base MvPolynomialClosure.MvPolynomial.homogeneousProjπ
  congr 2

theorem projectiveScalarMap_over {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (n : ℕ) :
    IntersectionTheory.ProjectionFormula.Relative.ProjectiveI.Scalars.map f n ≫ MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) =
      MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := S) ≫ Spec.map (CommRingCat.ofHom f) := by
  simpa only [relativeProjectiveBase_eq] using IntersectionTheory.ProjectionFormula.Relative.ProjectiveI.Base.scalar_over f n

def projectiveScalarMap_bundleIso {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (n : ℕ) (j l : Fin (n + 1)) :
    (Scheme.Modules.pullback (IntersectionTheory.ProjectionFormula.Relative.ProjectiveI.Scalars.map f n)).obj
      (Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.bundle (R := R) j).sheaf ≅
        (Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.bundle (R := S) l).sheaf :=
  (CoordinateBundlePullback.coordinatePreservingMap_bundle_iso n (IntersectionTheory.ProjectionFormula.Relative.ProjectiveI.Scalars.graded f n)
    (IntersectionTheory.ProjectionFormula.Relative.ProjectiveI.Scalars.irrelevant_le f n) (fun i => MvPolynomial.map_X f i) j l).some

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.ScalarBundle
