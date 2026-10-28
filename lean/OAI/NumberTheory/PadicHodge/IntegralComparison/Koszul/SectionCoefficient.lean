import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.OrientedTopCohomology

/-! # Section Coefficient -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.SectionCoefficient

noncomputable section

/-! A point quotient identified with the base has a canonical scalar
coordinate for every original top Koszul class. Its representative is
the ordered wedge functional with that literal base coefficient. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.OrientedTopCohomology
variable (k A : Type u) [CommRing k] [CommRing A] [Algebra k A]
  {n : ℕ} (s : Fin n → A) (e : (A ⧸ OrientedTopCohomology.ideal A s) ≃ₐ[k] k)

def coefficient (x : (OrientedTopCohomology.dualComplex A s).homology n) : k := e ((OrientedTopCohomology.iso A s).hom x)

def representative (x : (OrientedTopCohomology.dualComplex A s).homology n) : (OrientedTopCohomology.dualComplex A s).X n :=
  (OrientedTopCohomology.evaluation A s).symm (algebraMap k A (coefficient k A s e x))

theorem quotient_scalar (r : k) : e (Ideal.Quotient.mk (OrientedTopCohomology.ideal A s) (algebraMap k A r)) = r := by
  change e (algebraMap k (A ⧸ OrientedTopCohomology.ideal A s) r) = r
  exact e.commutes r

theorem representative_evaluation (x : (OrientedTopCohomology.dualComplex A s).homology n) :
    OrientedTopCohomology.evaluation A s (representative k A s e x) = algebraMap k A (coefficient k A s e x) :=
  (OrientedTopCohomology.evaluation A s).apply_symm_apply _

theorem cycle_representative (x : (OrientedTopCohomology.dualComplex A s).homology n) :
    TopHomologyCokernel.cycleClass (OrientedTopCohomology.dualComplex A s) n (OrientedTopCohomology.outgoing_isZero A s)
      (representative k A s e x) = x := by
  apply (ConcreteCategory.bijective_of_isIso (OrientedTopCohomology.iso A s).hom).1
  have h := ConcreteCategory.congr_hom (OrientedTopCohomology.cycleClass_iso A s) (representative k A s e x)
  change (OrientedTopCohomology.iso A s).hom
    (TopHomologyCokernel.cycleClass (OrientedTopCohomology.dualComplex A s) n (OrientedTopCohomology.outgoing_isZero A s)
      (representative k A s e x)) = Ideal.Quotient.mk (OrientedTopCohomology.ideal A s)
        (OrientedTopCohomology.evaluation A s (representative k A s e x)) at h
  rw [h, representative_evaluation]
  apply e.injective
  exact quotient_scalar k A s e (coefficient k A s e x)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.SectionCoefficient
