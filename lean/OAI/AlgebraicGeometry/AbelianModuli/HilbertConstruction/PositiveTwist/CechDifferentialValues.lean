import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PositiveTwist.CechLinearFactors
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ordered.CoefficientCechDifferentialValues

/-! # Cech Differential Values -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PositiveTwist.CechDifferentialValues

noncomputable section

/-! The nonnegative-twist term equivalence carries each actual differential component to the ordered graded restriction sum. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

theorem positiveTwistCechTermEquiv_differential_value (d q : ℕ)
    (x : (((Projective.CoefficientCechFunctor.projectiveCoefficientCechFunctor I).obj (ProjectiveTwisting.Bundle.projectiveTwistingBundle I d).sheaf).X q))
    (a : Ordered.SectionCechIndices.OrderedCechIndex (ULift.{u} (Fin (n + 1))) (q + 1)) :
    (CechTermEquivalence.positiveTwistCechTermEquiv I d (q + 1)
      (Ordered.CoefficientCechComplex.orderedCoefficientCechDifferential (Coefficient.ModulePresheaf.schemeCoefficientMap (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)))
        (ProjectiveTwisting.Bundle.projectiveTwistingBundle I d).sheaf (Projective.CechCover.projectiveCechOpens I) q x)).val (Projective.CechIntersectionCoordinates.projectiveCechIndexFinset a) =
      ∑ k : Fin (q + 2), (-1 : R) ^ k.val •
        HilbertScheme.Presentations.Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (NegativeTwist.CechCofaces.projectiveCechIndexFinset_delete_subset a k)
          ((CechTermEquivalence.positiveTwistCechTermEquiv I d q x).val (Projective.CechIntersectionCoordinates.projectiveCechIndexFinset (a.delete k))) := by
  let c := Coefficient.ModulePresheaf.schemeCoefficientMap (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))
  let L := (ProjectiveTwisting.Bundle.projectiveTwistingBundle I d).sheaf
  let U := Projective.CechCover.projectiveCechOpens I
  let v (k : Fin (q + 2)) := Pi.π
    (fun b : Ordered.SectionCechIndices.OrderedCechIndex (ULift.{u} (Fin (n + 1))) q ↦ Ordered.CoefficientCechTerms.coefficientCechFactor c L U q b.val)
    (a.delete k) x
  let w (k : Fin (q + 2)) := (Coefficient.ModulePresheaf.coefficientModulePresheaf c L).map
    (((FormalCoproduct.mk _ U).mapPower (SimplexCategory.δ k).toOrderHom.toFun).φ a.val).op (v k)
  let e := CechLinearFactors.positiveTwistCechFactorMap I d (q + 1) a
  let t (k : Fin (q + 2)) := HilbertScheme.Presentations.Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
    (NegativeTwist.CechCofaces.projectiveCechIndexFinset_delete_subset a k)
      ((CechTermEquivalence.positiveTwistCechTermEquiv I d q x).val (Projective.CechIntersectionCoordinates.projectiveCechIndexFinset (a.delete k)))
  have ht := CechTermValues.positiveTwistCechTermEquiv_value I d (q + 1)
    (Ordered.CoefficientCechComplex.orderedCoefficientCechDifferential c L U q x) a
  have hc := Ordered.CoefficientCechDifferentialValues.orderedCoefficientCechDifferential_value c L U q a x
  have hs : e (∑ k : Fin (q + 2), (-1 : ℤ) ^ k.val • w k) =
      ∑ k : Fin (q + 2), e ((-1 : ℤ) ^ k.val • w k) := map_sum e _ _
  have hk (k : Fin (q + 2)) : e (w k) = t k :=
    (CechCofaces.positiveTwistCechFactorEquiv_coface I d q a k (v k)).trans
      (congrArg (HilbertScheme.Presentations.Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
        (NegativeTwist.CechCofaces.projectiveCechIndexFinset_delete_subset a k))
        (CechTermValues.positiveTwistCechTermEquiv_value I d q x (a.delete k)).symm)
  have hz (k : Fin (q + 2)) : e ((-1 : ℤ) ^ k.val • w k) = (-1 : R) ^ k.val • t k := by
    calc
      _ = (-1 : ℤ) ^ k.val • e (w k) := map_zsmul e _ _
      _ = (-1 : ℤ) ^ k.val • t k := congrArg (fun y ↦ (-1 : ℤ) ^ k.val • y) (hk k)
      _ = (((-1 : ℤ) ^ k.val : ℤ) : R) • t k := (Int.cast_smul_eq_zsmul R _ _).symm
      _ = (-1 : R) ^ k.val • t k := by simp only [Int.cast_pow, Int.cast_neg, Int.cast_one]
  exact ht.trans ((congrArg e hc).trans (hs.trans (Finset.sum_congr rfl (fun k _ ↦ hz k))))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PositiveTwist.CechDifferentialValues
