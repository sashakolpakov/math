import OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Resolution

/-! # Ideal -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPoint.Ideal

noncomputable section

/-! The oriented product-basis point ideal is literally the ideal
of the concatenated normal and point parameters. -/
universe u
variable (R : Type u) [CommRing R] {c m : ℕ} (s : Fin c → R) (t : Fin m → R)

theorem append : KoszulPartial.Resolution.pointIdeal R s t =
    Koszul.OrientedTopCohomology.ideal R (Fin.append s t) := by
  change Ideal.span (Set.range (fun i => KoszulPartial.Differential.equation R s t
    (KoszulPartial.TopResidue.basis R i))) = _
  rw [KoszulPartial.Resolution.basis_values]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPoint.Ideal
