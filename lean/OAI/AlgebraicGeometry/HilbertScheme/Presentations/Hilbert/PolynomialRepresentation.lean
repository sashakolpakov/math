import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ArbitraryClassification
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.PolynomialTransformation
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.ProjectivePresentation
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.UnrealizableRepresentation

/-! # Polynomial Representation -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.PolynomialRepresentation.GradedHilbert

noncomputable section

/-! The constructed projective Hilbert scheme represents the exact
polynomial subfunctor on all test schemes. Unrealizable polynomials
are represented by the empty projective scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} [IsLocallyNoetherian S] {n N : ℕ}
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem boundedHilbertPolynomialTransformation_isIso
    (P : Polynomial ℚ)
    (hP : BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n N (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P) P)
    (hN : Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N)
    (hr : Fintype.card ι = (P.eval (N : ℚ)).num.toNat) :
    IsIso (BoundedHilbert.PolynomialTransformation.GradedHilbert.boundedHilbertPolynomialTransformation (ι := ι) n N S
      (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P) P hP) := by
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro T
  apply (isIso_iff_bijective _).mpr
  constructor
  · intro x y h
    exact ArbitraryInjectivity.GradedHilbert.boundedHilbertUniversalFamily_injective P hP hN hr T.unop (congrArg Subtype.val h)
  · intro F
    obtain ⟨x, hx, _⟩ := ArbitraryClassification.GradedHilbert.existsUnique_arbitrary_exact_hilbert_parameter F.val P F.property hN hr
    exact ⟨x, Subtype.ext hx⟩

def boundedHilbertPolynomialRepresentation
    (P : Polynomial ℚ)
    (hP : BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n N (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P) P)
    (hN : Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N)
    (hr : Fintype.card ι = (P.eval (N : ℚ)).num.toNat) :
    yoneda.obj (BoundedHilbert.Data.GradedHilbert.boundedHilbertOver (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P)) ≅
      (PolynomialSubfunctor.Core.hilbertPolynomialSubfunctor (Intrinsic.ProjectivePresentation.GradedHilbert.canonicalProjectivePresentation S n) P).toFunctor := by
  let := boundedHilbertPolynomialTransformation_isIso (S := S) (ι := ι) P hP hN hr
  exact asIso (BoundedHilbert.PolynomialTransformation.GradedHilbert.boundedHilbertPolynomialTransformation (ι := ι) n N S
    (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P) P hP)

theorem exists_projectiveSpace_hilbert_representation (S : Scheme.{u}) [IsLocallyNoetherian S]
    (n : ℕ) (P : Polynomial ℚ) :
    ∃ H : Over S, Has.Core.IsProjectiveOver H ∧
      Nonempty (yoneda.obj H ≅
        (PolynomialSubfunctor.Core.hilbertPolynomialSubfunctor (Intrinsic.ProjectivePresentation.GradedHilbert.canonicalProjectivePresentation S n) P).toFunctor) := by
  classical
  let N := Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P
  let ι : Type u := ULift.{u} (Fin (P.eval (N : ℚ)).num.toNat)
  have hr : Fintype.card ι = (P.eval (N : ℚ)).num.toNat := by simp [ι]
  have hN : Truncation.GradedHilbert.hilbertParameterDegree.{u} n P ≤ N := le_max_right _ _
  by_cases hP : BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n N (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P) P
  · refine ⟨BoundedHilbert.Data.GradedHilbert.boundedHilbertOver (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P),
      BoundedHilbert.ProjectivePresentation.GradedHilbert.boundedHilbert_isProjectiveOver P hP hN hr, ?_⟩
    exact ⟨boundedHilbertPolynomialRepresentation (S := S) (ι := ι) P hP le_rfl hr⟩
  · exact ⟨EmptyProjectiveParameter.Core.emptyParameterOver S, EmptyProjectiveParameter.Core.emptyParameter_isProjectiveOver S,
      ⟨UnrealizableRepresentation.Core.unrealizableHilbertPolynomialRepresentation (Intrinsic.ProjectivePresentation.GradedHilbert.canonicalProjectivePresentation S n) P N hN hP⟩⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.PolynomialRepresentation.GradedHilbert
