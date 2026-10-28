import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.GoingDown

/-! # Flat Prime Extension -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.FlatPrimeExtension.BundleCycles

noncomputable section

/-! Flat prime extension preserves height when extension and contraction
agree. Height-one primes meeting the base are then extended primes. -/

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S]

theorem flatPrimeExtension_height (p : Ideal R) [p.IsPrime]
    [(p.map (algebraMap R S)).IsPrime]
    (hp : Ideal.comap (algebraMap R S) (p.map (algebraMap R S)) = p) :
    (p.map (algebraMap R S)).height = p.height := by
  let : (p.map (algebraMap R S)).LiesOver p := ⟨hp.symm⟩
  have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p (p.map (algebraMap R S))
  simpa only [Ideal.map_quotient_self, Ideal.height_bot, add_zero] using h

theorem flatHeightOne_isExtended [IsDomain R]
    (P : Ideal S) [P.IsPrime] [((P.comap (algebraMap R S)).map (algebraMap R S)).IsPrime]
    (hP : P.height = 1) (hp : P.comap (algebraMap R S) ≠ ⊥)
    (hcomp : Ideal.comap (algebraMap R S) ((P.comap (algebraMap R S)).map (algebraMap R S)) =
      P.comap (algebraMap R S)) : (P.comap (algebraMap R S)).map (algebraMap R S) = P := by
  let p := P.comap (algebraMap R S)
  have hle : p.map (algebraMap R S) ≤ P := Ideal.map_comap_le
  have hpheight : 1 ≤ p.height :=
    Order.one_le_iff_ne_zero.mpr (Ideal.height_eq_zero_iff_eq_bot.not.mpr hp)
  apply Ideal.eq_of_le_of_height_le (p.map (algebraMap R S)) hle
  rw [flatPrimeExtension_height p hcomp, hP]
  exact hpheight

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.FlatPrimeExtension.BundleCycles
