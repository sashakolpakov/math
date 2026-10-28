import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.WeightedEuler
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LocalizedTorEuler

/-! # Tor Orders -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.TorOrders

noncomputable section

/-! Each family Tor module contributes its actual localized lengths
times the parameter orders, with finite support away from the closed
point. -/

open _root_.CategoryTheory IsLocalRing

universe u

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
  (M N : ModuleCat.{u} R) [Module.Finite R M] [Module.Finite R N] (r : R)
  (hisolated : (Module.support R M ∩ Module.support R N) ∩
    Module.support R (R ⧸ Ideal.span {r}) ⊆ {closedPoint R})

include hisolated

theorem exists_sum (hr : r ≠ 0) (hrm : r ∈ maximalIdeal R) (i : ℕ) :
    ∃ T : Finset (PrimeSpectrum R),
      (∀ p ∈ T, p ∈ Module.support R M ∩ Module.support R N ∧
        p ≠ closedPoint R ∧ r ∉ p.asIdeal) ∧
      (∀ p, p ≠ closedPoint R → p ∉ T →
        FiltrationBaseLength.length R (Localization.AtPrime p.asIdeal)
          (((Tor (ModuleCat R) i).obj M).obj N) = 0) ∧
      ProjectionFormula.Tor.Euler.euler R (((Tor (ModuleCat R) i).obj M).obj N)
        (.of R (R ⧸ Ideal.span {r})) 1 =
      ∑ p ∈ T, ((FiltrationBaseLength.length R (Localization.AtPrime p.asIdeal)
          (((Tor (ModuleCat R) i).obj M).obj N)).toNat : ℚ) *
        ((Ring.ord (R ⧸ p.asIdeal) (Ideal.Quotient.mk p.asIdeal r)).toNat : ℚ) := by
  let L := ((Tor (ModuleCat R) i).obj M).obj N
  let : Module.Finite R L := ProjectionFormula.Finite.Tor.finite R M N i
  have hsupp := ProjectionFormula.Tor.Support.support_subset R M N i
  have hiso : Module.support R L ∩ Module.support R (R ⧸ Ideal.span {r}) ⊆ {closedPoint R} :=
    fun _ hp => hisolated ⟨hsupp hp.1, hp.2⟩
  obtain ⟨T, hT, hout, he⟩ := WeightedEuler.exists_sum R L r hiso hr hrm
  refine ⟨T, fun p hp => ⟨hsupp (hT p hp).1, (hT p hp).2⟩, ?_, he⟩
  intro p hpn hpT
  by_cases hp : p ∈ Module.support R L
  · exact hout p hp hpn hpT
  · exact LocalizedTorEuler.length_zero R L p hp

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.TorOrders
