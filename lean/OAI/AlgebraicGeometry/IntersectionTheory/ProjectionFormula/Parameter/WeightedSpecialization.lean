import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.IsolatedEuler
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.TorOrders

/-! # Weighted Specialization -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.WeightedSpecialization

noncomputable section

/-! The isolated parameter-fiber intersection multiplicity is a
finite sum of actual localized family Tor Euler characteristics,
weighted by the parameter orders on the corresponding prime quotients. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory IsLocalRing
open scoped Classical

universe u

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
  (M N : ModuleCat.{u} R) [Module.Finite R M] [Module.Finite R N] (r : R)

def coefficient (p : PrimeSpectrum R) (d : ℕ) : ℚ :=
  ProjectionFormula.Tor.Euler.euler (Localization.AtPrime p.asIdeal)
    ((Flat.Extension.baseChange R (Localization.AtPrime p.asIdeal)).obj M)
    ((Flat.Extension.baseChange R (Localization.AtPrime p.asIdeal)).obj N) d

theorem exists_sum (hr : r ≠ 0) (hrm : r ∈ maximalIdeal R)
    (hM : IsSMulRegular M r) (hN : IsSMulRegular N r)
    (d : ℕ) [HasProjectiveDimensionLE N d]
    (hisolated : (Module.support R M ∩ Module.support R N) ∩
      Module.support R (R ⧸ Ideal.span {r}) ⊆ {closedPoint R}) :
    ∃ T : Finset (PrimeSpectrum R),
      (∀ p ∈ T, p ∈ Module.support R M ∩ Module.support R N ∧
        p ≠ closedPoint R ∧ r ∉ p.asIdeal) ∧
      (∀ p, p ≠ closedPoint R → p ∉ T → coefficient R M N p d = 0) ∧
      ProjectionFormula.Tor.Euler.euler (ScalarQuotient.Ring R r)
        ((ScalarQuotient.quotient R r).obj M)
        ((ScalarQuotient.quotient R r).obj N) d =
      ∑ p ∈ T, coefficient R M N p d *
        ((Ring.ord (R ⧸ p.asIdeal) (Ideal.Quotient.mk p.asIdeal r)).toNat : ℚ) := by
  choose U hU hout he using
    fun i => TorOrders.exists_sum R M N r hisolated hr hrm i
  let T := (Finset.range (d + 1)).biUnion U
  have hUT (i : ℕ) (hi : i ∈ Finset.range (d + 1)) : U i ⊆ T :=
    fun _ hp => Finset.mem_biUnion.mpr ⟨i, hi, hp⟩
  have hT (p : PrimeSpectrum R) (hp : p ∈ T) :
      p ∈ Module.support R M ∩ Module.support R N ∧ p ≠ closedPoint R ∧ r ∉ p.asIdeal := by
    obtain ⟨i, _, hpi⟩ := Finset.mem_biUnion.mp hp
    exact hU i p hpi
  refine ⟨T, hT, ?_, ?_⟩
  · intro p hpn hpT
    rw [coefficient, LocalizedTorEuler.euler]
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
    rw [IsolatedEuler.euler R r M N (IsSMulRegular.of_ne_zero hr)
      hM hN d (closedPoint R) hisolated]
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
        rw [coefficient, LocalizedTorEuler.euler]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.WeightedSpecialization
