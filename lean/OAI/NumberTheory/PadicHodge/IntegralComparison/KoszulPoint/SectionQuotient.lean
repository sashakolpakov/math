import OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPoint.Ideal

/-! # Section Quotient -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPoint.SectionQuotient

noncomputable section

/-! The canonical base quotient is unchanged when passing between the
product-basis point resolution and the concatenated ordered equations. -/
universe u
variable (k R : Type u) [CommRing k] [CommRing R] [Algebra k R]
  {c m : ℕ} (s : Fin c → R) (t : Fin m → R)
  (e : (R ⧸ Koszul.OrientedTopCohomology.ideal R (Fin.append s t)) ≃ₐ[k] k)

def equiv : (R ⧸ KoszulPartial.Resolution.pointIdeal R s t) ≃ₐ[k] k :=
  (Ideal.quotientEquivAlgOfEq k (KoszulPoint.Ideal.append R s t)).trans e

theorem equiv_mk (a : R) :
    equiv k R s t e (Ideal.Quotient.mk (KoszulPartial.Resolution.pointIdeal R s t) a) =
      e (Ideal.Quotient.mk (Koszul.OrientedTopCohomology.ideal R (Fin.append s t)) a) := by
  change e ((Ideal.quotientEquivAlgOfEq k (KoszulPoint.Ideal.append R s t)) _) = _
  rw [Ideal.quotientEquivAlgOfEq_mk]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPoint.SectionQuotient
