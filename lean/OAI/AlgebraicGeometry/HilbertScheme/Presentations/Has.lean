import OAI.AlgebraicGeometry.HilbertScheme.Presentations.HomFunctor
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ChartHomogeneousIdeal
import Mathlib.CategoryTheory.Subfunctor.Basic

/-! # Has -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Has.Core

noncomputable section

/-! Native geometric predicates for the statement of Presentations. No parameter scheme,
representability, or base-change theorem is assumed in these definitions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert

def projectiveSpaceMap (R : Type u) [CommRing R] (d : ℕ) :
    Proj (Hilbert.Polynomial.GradedHilbert.grading R d) ⟶ Spec (CommRingCat.of R) :=
  Proj.toSpecZero (Hilbert.Polynomial.GradedHilbert.grading R d) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (Hilbert.Polynomial.GradedHilbert.grading R d 0)))

def projectiveSpace (S : Scheme.{u}) (d : ℕ) : Scheme.{u} :=
  pullback (projectiveSpaceMap Γ(S, ⊤) d) S.toSpecΓ

def projectiveSpaceProjection (S : Scheme.{u}) (d : ℕ) : projectiveSpace S d ⟶ S :=
  pullback.snd _ _

/-- A chosen projective embedding, with its ordinary scheme-theoretic meaning. -/
structure ProjectivePresentation {S : Scheme.{u}} (X : Over S) where
  dimension : ℕ
  embedding : X.left ⟶ projectiveSpace S dimension
  closed : IsClosedImmersion embedding
  over_base : embedding ≫ projectiveSpaceProjection S dimension = X.hom

/-- Geometric projectivity, expressed by existence of a finite projective embedding. -/
def IsProjectiveOver {S : Scheme.{u}} (X : Over S) : Prop :=
  Nonempty (ProjectivePresentation X)

/-- The polynomial of a closed family is tested on every field-valued base
point. The coordinate comparison is an actual cartesian square with polynomial
Proj; the homogeneous ideal is constructed from the actual closed immersion.
Allowing any such comparison does not choose a coordinate trivialization. -/
def HasFiberHilbertPolynomial {S : Scheme.{u}} {X : Over S}
    (B : ProjectivePresentation X) {T : Over S} (I : Hilbert.Functor.Family X T)
    (P : Polynomial ℚ) : Prop :=
  ∀ (K : Type u) [Field K] (a : Spec (CommRingCat.of K) ⟶ T.left),
    let t : Over S := Over.mk (a ≫ T.hom)
    let b : t ⟶ T := Over.homMk a rfl
    let J := Hilbert.Functor.pullbackFamily X b I
    ∃ (q : Proj (Hilbert.Polynomial.GradedHilbert.grading K B.dimension) ⟶ projectiveSpace S B.dimension)
      (e : J.val.subscheme ⟶ Proj (Hilbert.Polynomial.GradedHilbert.grading K B.dimension)),
      IsPullback q (projectiveSpaceMap K B.dimension)
        (projectiveSpaceProjection S B.dimension) (a ≫ T.hom) ∧
      IsClosedImmersion e ∧
      e ≫ q = J.val.subschemeι ≫ (prod.snd : t ⨯ X ⟶ X).left ≫ B.embedding ∧
      e ≫ projectiveSpaceMap K B.dimension = Hilbert.Functor.familyProjection X J.val ∧
      Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf e.ker).toIdeal P

/-- Finite tuples in a functor, with the actual componentwise pullback maps. -/
def tupleFunctor {C : Type v} [Category.{u} C] (F : C ⥤ Type u) (n : ℕ) : C ⥤ Type u where
  obj T := Fin n → F.obj T
  map a := ↾fun f i => F.map a (f i)
  map_id T := by ext f i; exact ConcreteCategory.congr_hom (F.map_id T) (f i)
  map_comp a b := by ext f i; exact ConcreteCategory.congr_hom (F.map_comp a b) (f i)

def tupleNatTrans {C : Type v} [Category.{u} C] {F G : C ⥤ Type u}
    (f : F ⟶ G) (n : ℕ) : tupleFunctor F n ⟶ tupleFunctor G n where
  app T := ↾fun x i => f.app T (x i)
  naturality _ _ a := by
    apply ConcreteCategory.hom_ext
    intro x
    funext i
    exact ConcreteCategory.congr_hom (f.naturality a) (x i)

variable {S : Scheme.{u}} (X Y : Over S) (n : ℕ)

abbrev hilbertTuples := tupleFunctor (Hilbert.Functor.familyFunctor (X ⨯ Y)) n

abbrev morphismTuples := tupleFunctor (HomFunctor.Hom.morphismFunctor X Y) n

def HasHilbertPolynomials (B : ProjectivePresentation (X ⨯ Y))
    (P : Fin n → Polynomial ℚ) {T : Over S}
    (I : (hilbertTuples X Y n).obj (.op T)) : Prop :=
  ∀ i, HasFiberHilbertPolynomial B (I i) (P i)

def HasGraphPolynomials (B : ProjectivePresentation (X ⨯ Y))
    (P : Fin n → Polynomial ℚ) [Flat X.hom] [IsProper X.hom]
    [LocallyOfFinitePresentation X.hom] [IsSeparated Y.hom]
    {T : Over S} (f : (morphismTuples X Y n).obj (.op T)) : Prop :=
  ∀ i, HasFiberHilbertPolynomial B (HomFunctor.Hom.graphFamily X Y (f i)) (P i)

def graphs [Flat X.hom] [IsProper X.hom] [LocallyOfFinitePresentation X.hom]
    [IsSeparated Y.hom] : morphismTuples X Y n ⟶ hilbertTuples X Y n :=
  tupleNatTrans (HomFunctor.Hom.graphs X Y) n

/-- A Hilbert tuple lies in the graph locus exactly when every first projection
is an isomorphism of schemes, including over nonreduced test schemes. -/
def IsGraphTuple {T : Over S} (I : (hilbertTuples X Y n).obj (.op T)) : Prop :=
  ∀ i, IsIso ((I i).val.subschemeι ≫ (HomFunctor.Hom.graphProjection X Y T).left)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Has.Core
