import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Has

/-! # Fiber Polynomial Base Change -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.FiberPolynomialBaseChange.Core

noncomputable section

/-! The exact native field-fiber Hilbert-polynomial predicate is preserved
by arbitrary changes of test scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} {X : Over S} (B : Has.Core.ProjectivePresentation X)
variable {T U : Over S} (f : U ⟶ T) (I : Hilbert.Functor.Family X T) (P : Polynomial ℚ)

theorem hasFiberHilbertPolynomial_at (hI : Has.Core.HasFiberHilbertPolynomial B I P)
    (K : Type u) [Field K] (a : Spec (CommRingCat.of K) ⟶ T.left)
    (b : Spec (CommRingCat.of K) ⟶ S) (ha : a ≫ T.hom = b) :
    let t : Over S := Over.mk b
    let j : t ⟶ T := Over.homMk a ha
    let J := Hilbert.Functor.pullbackFamily X j I
    ∃ (q : Proj (Hilbert.Polynomial.GradedHilbert.grading K B.dimension) ⟶ Has.Core.projectiveSpace S B.dimension)
      (e : J.val.subscheme ⟶ Proj (Hilbert.Polynomial.GradedHilbert.grading K B.dimension)),
      IsPullback q (Has.Core.projectiveSpaceMap K B.dimension) (Has.Core.projectiveSpaceProjection S B.dimension) b ∧
      IsClosedImmersion e ∧
      e ≫ q = J.val.subschemeι ≫ (prod.snd : t ⨯ X ⟶ X).left ≫ B.embedding ∧
      e ≫ Has.Core.projectiveSpaceMap K B.dimension = Hilbert.Functor.familyProjection X J.val ∧
      Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf e.ker).toIdeal P := by
  subst b
  exact hI K a

theorem hasFiberHilbertPolynomial_pullback (hI : Has.Core.HasFiberHilbertPolynomial B I P) :
    Has.Core.HasFiberHilbertPolynomial B (Hilbert.Functor.pullbackFamily X f I) P := by
  intro K _ a
  have hbase : (a ≫ f.left) ≫ T.hom = a ≫ U.hom :=
    (Category.assoc _ _ _).trans (congrArg (fun g => a ≫ g) f.w)
  have h := hasFiberHilbertPolynomial_at B I P hI K (a ≫ f.left) (a ≫ U.hom) hbase
  dsimp only at h ⊢
  rw [← Hilbert.Functor.pullbackFamily_comp]
  have he : (Over.homMk a rfl : Over.mk (a ≫ U.hom) ⟶ U) ≫ f =
      Over.homMk (a ≫ f.left) ((Category.assoc _ _ _).trans (congrArg (fun g => a ≫ g) f.w)) :=
    Over.OverMorphism.ext rfl
  rw [he]
  exact h

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.FiberPolynomialBaseChange.Core
