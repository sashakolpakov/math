import OAI.AlgebraicGeometry.HilbertScheme.Presentations.NaturalEndomorphismClosedLocus
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.EndomorphismPolynomialSubfunctors
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.HomExactSubfunctors
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.RepresentedSubfunctorRange

/-! # Endomorphism Closed Locus -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations

noncomputable section

/-! The exact polynomial-restricted endomorphism functor is represented
by a closed subscheme of any Hilbert/Hom package's morphism scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable (A : Over S) [GrpObj A]
variable [Flat A.hom] [IsProper A.hom] [LocallyOfFinitePresentation A.hom]
variable {B : Has.Core.ProjectivePresentation (A ⨯ A)} {n : ℕ} {P : Fin n → Polynomial ℚ}

theorem Loci.Core.HilbertHomLoci.endomorphism_closed_locus
    (BA : Has.Core.ProjectivePresentation A) (L : Loci.Core.HilbertHomLoci A A B n P) :
    ∃ (E : Over S) (j : E ⟶ L.homScheme), IsClosedImmersion j.left ∧
      ∃ e : yoneda.obj E ≅ (EndomorphismPolynomialSubfunctors.Core.endomorphismPolynomialSubfunctor A n B P).toFunctor,
        e.hom ≫ (EndomorphismPolynomialSubfunctors.Core.endomorphismPolynomialSubfunctor A n B P).ι ≫ Endomorphisms.Core.forgetGroupLaw A n =
          yoneda.map j ≫ L.morphismEquivalence.hom ≫ L.morphismLocus.ι := by
  let : LocallyOfFiniteType L.homScheme.hom := L.hom_finiteType
  let : IsLocallyNoetherian L.homScheme.left :=
    LocallyOfFiniteType.isLocallyNoetherian L.homScheme.hom
  let t : yoneda.obj L.homScheme ⟶ Has.Core.morphismTuples A A n :=
    L.morphismEquivalence.hom ≫ L.morphismLocus.ι
  obtain ⟨E, j, hj, _, e, he⟩ := NaturalEndomorphismClosedLocus.Core.naturalMorphism_endomorphismClosed A n BA t
  have hrange : Subfunctor.range t = L.morphismLocus :=
    RepresentedSubfunctorRange.representedSubfunctor_range L.morphismLocus L.morphismEquivalence
  have h : (Subfunctor.range t).preimage (Endomorphisms.Core.forgetGroupLaw A n) =
      EndomorphismPolynomialSubfunctors.Core.endomorphismPolynomialSubfunctor A n B P := by
    rw [hrange, L.morphismLocus_eq]
    rfl
  obtain ⟨e', he'⟩ := RepresentedSubfunctorRange.representedSubfunctor_transport h
    (e.hom ≫ ((Subfunctor.range t).preimage (Endomorphisms.Core.forgetGroupLaw A n)).ι) e rfl
  refine ⟨E, j, hj, e', ?_⟩
  have hc := congrArg (fun k => k ≫ Endomorphisms.Core.forgetGroupLaw A n) he'
  have hc' : e'.hom ≫ (EndomorphismPolynomialSubfunctors.Core.endomorphismPolynomialSubfunctor A n B P).ι ≫ Endomorphisms.Core.forgetGroupLaw A n =
      e.hom ≫ ((Subfunctor.range t).preimage (Endomorphisms.Core.forgetGroupLaw A n)).ι ≫ Endomorphisms.Core.forgetGroupLaw A n := by
    simpa only [Category.assoc] using hc
  exact hc'.trans he

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations
