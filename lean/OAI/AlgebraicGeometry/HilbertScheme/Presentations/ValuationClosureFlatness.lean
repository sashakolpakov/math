import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ContractedHomogeneousQuotient
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.Flatness
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.QuotientRetraction
import Mathlib.RingTheory.LocalRing.Module

/-! # Valuation Closure Flatness -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.ValuationClosureFlatness.GradedHilbert

noncomputable section

/-! Contracting a homogeneous ideal from the fraction field of a valuation
ring gives flat coordinate quotients in every degree and a flat Proj. -/

universe u
variable {R K : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K] {n : ℕ}
variable (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n))

theorem valuationClosure_degree_flat (d : ℕ) :
    Module.Flat R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient (ContractedHomogeneousQuotient.GradedHilbert.contractedHomogeneousIdeal (R := R) I).toIdeal d) := by
  let : Module.IsTorsionFree R (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n ⧸ I.toIdeal) := Module.IsTorsionFree.trans K
  let := ContractedHomogeneousQuotient.GradedHilbert.contractedDegreeQuotient_isTorsionFree (R := R) I d
  apply Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.mpr
  exact Submodule.isTorsionFree_iff_torsion_eq_bot.mp inferInstance

theorem valuationClosure_degree_free (d : ℕ) :
    Module.Free R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient (ContractedHomogeneousQuotient.GradedHilbert.contractedHomogeneousIdeal (R := R) I).toIdeal d) := by
  let := valuationClosure_degree_flat (R := R) I d
  exact Module.free_of_flat_of_isLocalRing

theorem valuationClosure_projective_flat :
    AlgebraicGeometry.Flat (Projective.Flatness.GradedHilbert.projectiveStructureMap
      (Graded.Quotient.GradedHilbert.quotientGrading (ContractedHomogeneousQuotient.GradedHilbert.contractedHomogeneousIdeal (R := R) I))) :=
  Projective.Flatness.GradedHilbert.projectiveQuotient_flat_of_eventually_flat _ 0 (fun d _ => valuationClosure_degree_flat I d)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.ValuationClosureFlatness.GradedHilbert
