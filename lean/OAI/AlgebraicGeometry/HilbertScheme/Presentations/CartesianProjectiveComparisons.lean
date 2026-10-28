import OAI.AlgebraicGeometry.HilbertScheme.Presentations.CanonicalFiberPolynomial
import OAI.AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions

/-! # Cartesian Projective Comparisons -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.CartesianProjectiveComparisons

noncomputable section

/-! Two arbitrary Cartesian projective coordinate comparisons differ
by an actual automorphism preserving the field base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.CanonicalFiberPolynomial.GradedHilbert

universe u
variable {S : Scheme.{u}} {K : Type u} [Field K] {n : ℕ}
variable (a : Spec (.of K) ⟶ S)
variable (q r : Proj (Hilbert.Polynomial.GradedHilbert.grading K n) ⟶ Has.Core.projectiveSpace S n)
variable (hq : IsPullback q (Has.Core.projectiveSpaceMap K n) (Has.Core.projectiveSpaceProjection S n) a)
variable (hr : IsPullback r (Has.Core.projectiveSpaceMap K n) (Has.Core.projectiveSpaceProjection S n) a)

def cartesianProjectiveComparisonIso : Proj (Hilbert.Polynomial.GradedHilbert.grading K n) ≅ Proj (Hilbert.Polynomial.GradedHilbert.grading K n) :=
  hq.isoIsPullback _ _ hr

theorem cartesianProjectiveComparisonIso_ambient :
    (cartesianProjectiveComparisonIso a q r hq hr).hom ≫ r = q := hq.isoIsPullback_hom_fst _ _ hr

theorem cartesianProjectiveComparisonIso_base :
    (cartesianProjectiveComparisonIso a q r hq hr).hom ≫ Has.Core.projectiveSpaceMap K n =
      Has.Core.projectiveSpaceMap K n := hq.isoIsPullback_hom_snd _ _ hr

theorem cartesianProjectiveComparisonIso_native_base :
    (cartesianProjectiveComparisonIso a q r hq hr).hom ≫ SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ =
      SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ := cartesianProjectiveComparisonIso_base a q r hq hr

theorem cartesianProjectiveComparisonIso_embedding {Z : Scheme.{u}}
    (f g : Z ⟶ Proj (Hilbert.Polynomial.GradedHilbert.grading K n)) (hqr : f ≫ q = g ≫ r)
    (hb : f ≫ Has.Core.projectiveSpaceMap K n = g ≫ Has.Core.projectiveSpaceMap K n) :
    f ≫ (cartesianProjectiveComparisonIso a q r hq hr).hom = g := by
  apply hr.hom_ext
  · rw [Category.assoc, cartesianProjectiveComparisonIso_ambient]
    exact hqr
  · rw [Category.assoc, cartesianProjectiveComparisonIso_base]
    exact hb

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.CartesianProjectiveComparisons
