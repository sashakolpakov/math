import OAI.AlgebraicGeometry.HilbertScheme.Presentations.UnrealizablePolynomialEmpty
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.EmptyIntrinsicFamilies
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.EmptyProjectiveParameter
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.PolynomialSubfunctor
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-! # Unrealizable Representation -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.UnrealizableRepresentation.Core

noncomputable section

/-! Unrealizable Hilbert polynomials have the actual empty projective
scheme as their representing object on every test scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} {X : Over S} (B : Has.Core.ProjectivePresentation X) (P : Polynomial ℚ)

def emptyPolynomialHilbertPointMap :
    yoneda.obj (EmptyProjectiveParameter.Core.emptyParameterOver S) ⟶ (Hilbert.PolynomialSubfunctor.Core.hilbertPolynomialSubfunctor B P).toFunctor where
  app T := ↾fun a => by
    let : IsEmpty T.unop.left := a.left.base.hom.1.isEmpty
    exact ⟨EmptyIntrinsicFamilies.Hilbert.emptyBaseFamily X T.unop,
      EmptyIntrinsicFamilies.Statement.emptyBaseFamily_hasFiberHilbertPolynomial B _ P⟩
  naturality T U a := by
    apply ConcreteCategory.hom_ext
    intro b
    apply Subtype.ext
    let : IsEmpty U.unop.left := (a.unop.left ≫ b.left).base.hom.1.isEmpty
    exact (EmptyIntrinsicFamilies.Hilbert.family_subsingleton_of_isEmpty X U.unop).elim _ _

theorem emptyPolynomialHilbertPointMap_isIso (N : ℕ)
    (hN : Hilbert.Truncation.GradedHilbert.hilbertParameterDegree.{u} B.dimension P ≤ N)
    (h : ¬ BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} B.dimension N
      (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} B.dimension N P) P) :
    IsIso (emptyPolynomialHilbertPointMap B P) := by
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro T
  apply (isIso_iff_bijective _).mpr
  constructor
  · intro a b _
    exact (EmptyProjectiveParameter.Core.emptyParameter_hom_subsingleton T.unop).elim a b
  · intro F
    let : IsEmpty T.unop.left := UnrealizablePolynomialEmpty.Core.polynomial_family_isEmpty_of_unrealizable B F.val P F.property N hN h
    refine ⟨EmptyProjectiveParameter.Core.emptyTestParameter T.unop, ?_⟩
    apply Subtype.ext
    exact (EmptyIntrinsicFamilies.Hilbert.family_subsingleton_of_isEmpty X T.unop).elim _ _

def unrealizableHilbertPolynomialRepresentation (N : ℕ)
    (hN : Hilbert.Truncation.GradedHilbert.hilbertParameterDegree.{u} B.dimension P ≤ N)
    (h : ¬ BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} B.dimension N
      (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} B.dimension N P) P) :
    yoneda.obj (EmptyProjectiveParameter.Core.emptyParameterOver S) ≅ (Hilbert.PolynomialSubfunctor.Core.hilbertPolynomialSubfunctor B P).toFunctor := by
  let := emptyPolynomialHilbertPointMap_isIso B P N hN h
  exact asIso (emptyPolynomialHilbertPointMap B P)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.UnrealizableRepresentation.Core
