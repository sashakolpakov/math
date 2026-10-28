import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.QuotientEuler
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.WeightedSpecialization

/-! # Weighted Principal Quotient -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.WeightedPrincipalQuotient

noncomputable section

/-! A principal quotient intersects another module as the finite
sum of parameter orders on the original intersection components,
weighted by their native generic Tor Euler characteristics. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory IsLocalRing
open scoped Classical

universe u

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.WeightedSpecialization

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
  (M N : ModuleCat.{u} R) [Module.Finite R M] [Module.Finite R N] (r : R)

theorem exists_sum (hr : r ≠ 0) (hrm : r ∈ maximalIdeal R)
    (hM : IsSMulRegular M r) (d : ℕ) [HasProjectiveDimensionLE N d]
    (hisolated : (Module.support R M ∩ Module.support R N) ∩
      Module.support R (R ⧸ Ideal.span {r}) ⊆ {closedPoint R}) :
    ∃ T : Finset (PrimeSpectrum R),
      (∀ p ∈ T, p ∈ Module.support R M ∩ Module.support R N ∧
        p ≠ closedPoint R ∧ r ∉ p.asIdeal) ∧
      (∀ p, p ≠ closedPoint R → p ∉ T → Parameter.WeightedSpecialization.coefficient R M N p d = 0) ∧
      ProjectionFormula.Tor.Euler.euler R (.of R (QuotSMulTop r M)) N d =
        ∑ p ∈ T, Parameter.WeightedSpecialization.coefficient R M N p d *
          ((Ring.ord (R ⧸ p.asIdeal) (Ideal.Quotient.mk p.asIdeal r)).toNat : ℚ) := by
  choose U hU hout he using
    fun i => Parameter.TorOrders.exists_sum R M N r hisolated hr hrm i
  let T := (Finset.range (d + 1)).biUnion U
  have hUT (i : ℕ) (hi : i ∈ Finset.range (d + 1)) : U i ⊆ T :=
    fun _ hp => Finset.mem_biUnion.mpr ⟨i, hi, hp⟩
  have hT (p : PrimeSpectrum R) (hp : p ∈ T) :
      p ∈ Module.support R M ∩ Module.support R N ∧ p ≠ closedPoint R ∧ r ∉ p.asIdeal := by
    obtain ⟨i, _, hpi⟩ := Finset.mem_biUnion.mp hp
    exact hU i p hpi
  refine ⟨T, hT, ?_, ?_⟩
  · intro p hpn hpT
    rw [Parameter.WeightedSpecialization.coefficient, LocalizedTorEuler.euler]
    apply Finset.sum_eq_zero
    intro i hi
    rw [hout i p hpn (fun hp => hpT (hUT i hi hp)), ENat.toNat_zero, Nat.cast_zero, mul_zero]
  · have hext (i : ℕ) (hi : i ∈ Finset.range (d + 1)) :
        ProjectionFormula.Tor.Euler.euler R (((Tor (ModuleCat R) i).obj M).obj N)
          (.of R (R ⧸ Ideal.span {r})) 1 =
        ∑ p ∈ T, ((FiltrationBaseLength.length R (Localization.AtPrime p.asIdeal)
            (((Tor (ModuleCat R) i).obj M).obj N)).toNat : ℚ) *
          ((Ring.ord (R ⧸ p.asIdeal) (Ideal.Quotient.mk p.asIdeal r)).toNat : ℚ) := by
      rw [he i]
      apply Finset.sum_subset (hUT i hi)
      intro p hpT hpi
      rw [hout i p (hT p hpT).2.1 hpi, ENat.toNat_zero, Nat.cast_zero, zero_mul]
    rw [Principal.QuotientEuler.isolated R r (IsSMulRegular.of_ne_zero hr)
      M N hM d (closedPoint R) hisolated]
    calc
      _ = ∑ i ∈ Finset.range (d + 1), ∑ p ∈ T,
          (-1 : ℚ) ^ i *
            (((FiltrationBaseLength.length R (Localization.AtPrime p.asIdeal)
              (((Tor (ModuleCat R) i).obj M).obj N)).toNat : ℚ) *
              ((Ring.ord (R ⧸ p.asIdeal) (Ideal.Quotient.mk p.asIdeal r)).toNat : ℚ)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hext i hi, Finset.mul_sum]
      _ = ∑ p ∈ T, (∑ i ∈ Finset.range (d + 1),
          (-1 : ℚ) ^ i *
            ((FiltrationBaseLength.length R (Localization.AtPrime p.asIdeal)
              (((Tor (ModuleCat R) i).obj M).obj N)).toNat : ℚ)) *
              ((Ring.ord (R ⧸ p.asIdeal) (Ideal.Quotient.mk p.asIdeal r)).toNat : ℚ) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro p _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        exact (mul_assoc _ _ _).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro p _
        rw [Parameter.WeightedSpecialization.coefficient, LocalizedTorEuler.euler]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.WeightedPrincipalQuotient
