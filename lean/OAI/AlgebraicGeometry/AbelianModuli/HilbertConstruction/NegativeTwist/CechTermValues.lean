import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NegativeTwist.CechTermEquivalence

/-! # Cech Term Values -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NegativeTwist.CechTermValues

noncomputable section

/-! The negative-twist Čech term equivalence evaluates to the constructed factor equivalence on every ordered intersection. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

theorem negativeTwistCechTermEquiv_value (d q : ℕ)
    (x : (((Projective.CoefficientCechFunctor.projectiveCoefficientCechFunctor I).obj (Negative.ProjectiveTwistingBundle.negativeProjectiveTwistingBundle I d).sheaf).X q))
    (a : Ordered.SectionCechIndices.OrderedCechIndex (ULift.{u} (Fin (n + 1))) q) :
    (CechTermEquivalence.negativeTwistCechTermEquiv I d q x).val (Projective.CechIntersectionCoordinates.projectiveCechIndexFinset a) =
      (CechTermEquivalence.negativeTwistCechFactorEquiv I d q a
        (Pi.π (fun b : Ordered.SectionCechIndices.OrderedCechIndex (ULift.{u} (Fin (n + 1))) q ↦
          Ordered.CoefficientCechTerms.coefficientCechFactor (Coefficient.ModulePresheaf.schemeCoefficientMap (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)))
            (Negative.ProjectiveTwistingBundle.negativeProjectiveTwistingBundle I d).sheaf (Projective.CechCover.projectiveCechOpens I) q b.val) a x)).val := by
  let P : {s : Finset (Fin (n + 1)) // s.card = q + 1} → Type u := fun s ↦
    HilbertScheme.Presentations.Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) s.val (-(d : ℤ))
  let eI : Ordered.SectionCechIndices.OrderedCechIndex (ULift.{u} (Fin (n + 1))) q ≃
      {s : Finset (Fin (n + 1)) // s.card = q + 1} :=
    OrderedCech.LiftedIndices.orderedCechLiftedFinsetEquiv (Fin (n + 1)) q
  let e₀ := Ordered.CoefficientCechTerms.orderedCoefficientCechObjectIsoPi
    (Coefficient.ModulePresheaf.schemeCoefficientMap (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)))
    (Negative.ProjectiveTwistingBundle.negativeProjectiveTwistingBundle I d).sheaf (Projective.CechCover.projectiveCechOpens I) q
  let y : ∀ b : Ordered.SectionCechIndices.OrderedCechIndex (ULift.{u} (Fin (n + 1))) q, P (eI b) :=
    fun b ↦ CechTermEquivalence.negativeTwistCechFactorEquiv I d q b (e₀.hom x b)
  let E := HilbertScheme.Presentations.ModuleCech.Terms.ProjectiveCech.moduleCechTermEquiv (σ := Fin (n + 1)) R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
    (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (-(d : ℤ)) (q + 1)
  have ht : (CechTermEquivalence.negativeTwistCechTermEquiv I d q x).val (Projective.CechIntersectionCoordinates.projectiveCechIndexFinset a) =
      ((LinearEquiv.piCongrLeft R P eI) y (eI a)).val :=
    congrArg (fun z ↦ (z (eI a)).val) (E.apply_symm_apply ((LinearEquiv.piCongrLeft R P eI) y))
  have hi : (LinearEquiv.piCongrLeft R P eI) y (eI a) = y a :=
    Equiv.piCongrLeft_apply_apply P eI y a
  have hπ : e₀.hom x a = Pi.π
      (fun b : Ordered.SectionCechIndices.OrderedCechIndex (ULift.{u} (Fin (n + 1))) q ↦
        Ordered.CoefficientCechTerms.coefficientCechFactor (Coefficient.ModulePresheaf.schemeCoefficientMap (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)))
          (Negative.ProjectiveTwistingBundle.negativeProjectiveTwistingBundle I d).sheaf (Projective.CechCover.projectiveCechOpens I) q b.val) a x :=
    ModuleCat.piIsoPi_hom_ker_subtype_apply _ a x
  exact ht.trans ((congrArg Subtype.val hi).trans
    (congrArg (fun z ↦ (CechTermEquivalence.negativeTwistCechFactorEquiv I d q a z).val) hπ))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NegativeTwist.CechTermValues
