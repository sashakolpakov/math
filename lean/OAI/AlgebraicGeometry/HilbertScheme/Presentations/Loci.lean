import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Segre.Open
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Endomorphisms

/-! # Loci -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Loci.Core

noncomputable section

/-! Complete existence packages used only in Presentations theorem conclusions. The
subfunctors are identified with the stated geometric predicates on every test
scheme, and all representing equivalences are natural isomorphisms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} (X Y : Over S)
variable [Flat X.hom] [IsProper X.hom] [LocallyOfFinitePresentation X.hom]
variable [IsSeparated Y.hom]

/-- All assertions of relative Hilbert/Hom representability and the open graph
locus. This is output data; none of these fields is a theorem hypothesis. -/
structure HilbertHomLoci (B : Has.Core.ProjectivePresentation (X ⨯ Y))
    (n : ℕ) (P : Fin n → Polynomial ℚ) where
  hilbert : Over S
  homScheme : Over S
  hilbertLocus : Subfunctor (Has.Core.hilbertTuples X Y n)
  morphismLocus : Subfunctor (Has.Core.morphismTuples X Y n)
  hilbert_mem : ∀ (T : Over S) (I : (Has.Core.hilbertTuples X Y n).obj (.op T)),
    I ∈ hilbertLocus.obj (.op T) ↔ Has.Core.HasHilbertPolynomials X Y n B P I
  morphism_mem : ∀ (T : Over S) (f : (Has.Core.morphismTuples X Y n).obj (.op T)),
    f ∈ morphismLocus.obj (.op T) ↔ Has.Core.HasGraphPolynomials X Y n B P f
  hilbertEquivalence : yoneda.obj hilbert ≅ hilbertLocus.toFunctor
  morphismEquivalence : yoneda.obj homScheme ≅ morphismLocus.toFunctor
  projective : Has.Core.IsProjectiveOver hilbert
  hom_finiteType : LocallyOfFiniteType homScheme.hom
  graphInclusion : homScheme ⟶ hilbert
  graph_open : IsOpenImmersion graphInclusion.left
  graph_compatibility : morphismEquivalence.hom ≫ morphismLocus.ι ≫ Has.Core.graphs X Y n =
    yoneda.map graphInclusion ≫ hilbertEquivalence.hom ≫ hilbertLocus.ι
  graph_image : ∀ (T : Over S) (x : T ⟶ hilbert),
    Has.Core.IsGraphTuple X Y n (hilbertEquivalence.hom.app (.op T) x).val ↔
      ∃! y : T ⟶ homScheme, y ≫ graphInclusion = x

variable (A : Over S) [GrpObj A]
variable [Flat A.hom] [IsProper A.hom] [LocallyOfFinitePresentation A.hom]
variable [IsSeparated A.hom]

/-- Closed group-compatibility and finite-equation loci in the actual graph
locus. Equations are imposed scheme-theoretically, on arbitrary test schemes. -/
structure EndomorphismEquationLoci (B : Has.Core.ProjectivePresentation (A ⨯ A))
    (n : ℕ) (P : Fin n → Polynomial ℚ) (L : HilbertHomLoci A A B n P)
    (R : Endomorphisms.Core.FiniteEndomorphismEquations A n) where
  endScheme : Over S
  solutionScheme : Over S
  endLocus : Subfunctor (Endomorphisms.Core.endomorphismTuples A n)
  solutionLocus : Subfunctor (Endomorphisms.Core.endomorphismTuples A n)
  end_mem : ∀ (T : Over S) (f : (Endomorphisms.Core.endomorphismTuples A n).obj (.op T)),
    f ∈ endLocus.obj (.op T) ↔
      Has.Core.HasGraphPolynomials A A n B P ((Endomorphisms.Core.forgetGroupLaw A n).app (.op T) f)
  solution_mem : ∀ (T : Over S) (f : (Endomorphisms.Core.endomorphismTuples A n).obj (.op T)),
    f ∈ solutionLocus.obj (.op T) ↔
      Has.Core.HasGraphPolynomials A A n B P ((Endomorphisms.Core.forgetGroupLaw A n).app (.op T) f) ∧
        Endomorphisms.Core.SatisfiesEquations R f
  endEquivalence : yoneda.obj endScheme ≅ endLocus.toFunctor
  solutionEquivalence : yoneda.obj solutionScheme ≅ solutionLocus.toFunctor
  forgetGroup : endScheme ⟶ L.homScheme
  forgetEquations : solutionScheme ⟶ endScheme
  group_closed : IsClosedImmersion forgetGroup.left
  equations_closed : IsClosedImmersion forgetEquations.left
  group_compatibility : endEquivalence.hom ≫ endLocus.ι ≫ Endomorphisms.Core.forgetGroupLaw A n =
    yoneda.map forgetGroup ≫ L.morphismEquivalence.hom ≫ L.morphismLocus.ι
  equations_compatibility : solutionEquivalence.hom ≫ solutionLocus.ι =
    yoneda.map forgetEquations ≫ endEquivalence.hom ≫ endLocus.ι

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Loci.Core
