import OAI.AlgebraicGeometry.HilbertScheme.Presentations.NaturalHomOpen
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.TupleSubfunctors
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Loci
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.PresentationProper
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.RepresentedSubfunctorRange

/-! # Hom Package Assembly -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.HomPackageAssembly.Core

noncomputable section

/-! Assemble the exact Hilbert/Hom package from a projective
representation of the polynomial Hilbert tuple subfunctor. The Hom scheme
is the proved graph open, with all natural compatibility equalities. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} [IsLocallyNoetherian S] (X Y : Over S)
variable [Flat X.hom] [IsProper X.hom] [LocallyOfFinitePresentation X.hom]
variable [IsSeparated Y.hom]
variable (B : Has.Core.ProjectivePresentation (X ⨯ Y)) (n : ℕ) (P : Fin n → Polynomial ℚ)

theorem hilbertHomLoci_of_projective_hilbert
    (H : Over S) (BH : Has.Core.ProjectivePresentation H)
    (eH : yoneda.obj H ≅ (Presentations.Polynomial.TupleSubfunctors.Core.hilbertPolynomialTupleSubfunctor X Y n B P).toFunctor) :
    Nonempty (Loci.Core.HilbertHomLoci X Y B n P) := by
  let : LocallyOfFiniteType H.hom := BH.locallyOfFiniteType
  let : IsLocallyNoetherian H.left := BH.locallyNoetherian
  let t : yoneda.obj H ⟶ Has.Core.hilbertTuples X Y n :=
    eH.hom ≫ (Presentations.Polynomial.TupleSubfunctors.Core.hilbertPolynomialTupleSubfunctor X Y n B P).ι
  obtain ⟨M, j, hj, hM, htest, e, he⟩ := NaturalHomOpen.Core.naturalHilbert_homOpen X Y n t
  have hrange : Subfunctor.range t = Presentations.Polynomial.TupleSubfunctors.Core.hilbertPolynomialTupleSubfunctor X Y n B P :=
    RepresentedSubfunctorRange.representedSubfunctor_range _ eH
  have h : (Subfunctor.range t).preimage (Has.Core.graphs X Y n) =
      Presentations.Polynomial.TupleSubfunctors.Core.morphismPolynomialTupleSubfunctor X Y n B P := by
    rw [hrange]
    rfl
  obtain ⟨eM, heM⟩ := RepresentedSubfunctorRange.representedSubfunctor_transport h
    (e.hom ≫ ((Subfunctor.range t).preimage (Has.Core.graphs X Y n)).ι) e rfl
  have hcomp : eM.hom ≫ (Presentations.Polynomial.TupleSubfunctors.Core.morphismPolynomialTupleSubfunctor X Y n B P).ι ≫ Has.Core.graphs X Y n =
      yoneda.map j ≫ eH.hom ≫ (Presentations.Polynomial.TupleSubfunctors.Core.hilbertPolynomialTupleSubfunctor X Y n B P).ι := by
    have hc : eM.hom ≫ (Presentations.Polynomial.TupleSubfunctors.Core.morphismPolynomialTupleSubfunctor X Y n B P).ι ≫ Has.Core.graphs X Y n =
        e.hom ≫ ((Subfunctor.range t).preimage (Has.Core.graphs X Y n)).ι ≫ Has.Core.graphs X Y n := by
      simpa only [Category.assoc] using congrArg (fun k => k ≫ Has.Core.graphs X Y n) heM
    exact hc.trans he
  exact ⟨{
    hilbert := H
    homScheme := M
    hilbertLocus := Presentations.Polynomial.TupleSubfunctors.Core.hilbertPolynomialTupleSubfunctor X Y n B P
    morphismLocus := Presentations.Polynomial.TupleSubfunctors.Core.morphismPolynomialTupleSubfunctor X Y n B P
    hilbert_mem := fun _ _ => Iff.rfl
    morphism_mem := fun _ _ => Iff.rfl
    hilbertEquivalence := eH
    morphismEquivalence := eM
    projective := ⟨BH⟩
    hom_finiteType := hM
    graphInclusion := j
    graph_open := hj
    graph_compatibility := hcomp
    graph_image := htest }⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.HomPackageAssembly.Core
