import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Has
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.DegreeRankProfile
import Mathlib.AlgebraicGeometry.ResidueField

/-! # Unrealizable Polynomial Empty -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.UnrealizablePolynomialEmpty.Core

noncomputable section

/-! An unrealizable polynomial admits no native family over a nonempty
test scheme. This uses the exact statement predicate, with arbitrary Cartesian coordinates. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert
universe u
variable {S : Scheme.{u}} {X T : Over S}

theorem rankProfileRealizes_of_polynomial_family_at_point
    (B : Has.Core.ProjectivePresentation X) (F : Hilbert.Functor.Family X T) (P : Polynomial ℚ)
    (hP : Has.Core.HasFiberHilbertPolynomial B F P) (N : ℕ)
    (hN : Hilbert.Truncation.GradedHilbert.hilbertParameterDegree.{u} B.dimension P ≤ N) (t : T.left) :
    BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} B.dimension N (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} B.dimension N P) P := by
  obtain ⟨q, e, _, _, _, _, hp⟩ := hP (T.left.residueField t) (T.left.fromSpecResidueField t)
  exact Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile_realizes (ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf e.ker)
    (ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf_saturated _) P hp N hN

theorem polynomial_family_isEmpty_of_unrealizable
    (B : Has.Core.ProjectivePresentation X) (F : Hilbert.Functor.Family X T) (P : Polynomial ℚ)
    (hP : Has.Core.HasFiberHilbertPolynomial B F P) (N : ℕ)
    (hN : Hilbert.Truncation.GradedHilbert.hilbertParameterDegree.{u} B.dimension P ≤ N)
    (h : ¬ BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} B.dimension N
      (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} B.dimension N P) P) : IsEmpty T.left :=
  ⟨fun t => h (rankProfileRealizes_of_polynomial_family_at_point B F P hP N hN t)⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.UnrealizablePolynomialEmpty.Core
