import OAI.AlgebraicGeometry.Divisors.LineBundles.FlatOrderEq
import Mathlib.RingTheory.RingHom.Flat

/-! # Flat Extended Prime Order -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.FlatExtendedPrimeOrder.BundleCycles

noncomputable section

/-!
# LineBundleCycles: local orders at extended primes of a flat algebra
-/

universe u

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.IsPrime]
    (hp : p = Ideal.comap (algebraMap R S) P)

theorem extendedPrimeLocalMap_maximalIdeal (hP : p.map (algebraMap R S) = P) :
    (IsLocalRing.maximalIdeal (Localization.AtPrime p)).map
      (Localization.localRingHom p P (algebraMap R S) hp) =
        IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
  have hc : (Localization.localRingHom p P (algebraMap R S) hp).comp
      (algebraMap R (Localization.AtPrime p)) =
        (algebraMap S (Localization.AtPrime P)).comp (algebraMap R S) := by
    ext a
    exact Localization.localRingHom_to_map p P (algebraMap R S) hp a
  rw [← Localization.AtPrime.map_eq_maximalIdeal (I := p), Ideal.map_map, hc,
    ← Ideal.map_map, hP, Localization.AtPrime.map_eq_maximalIdeal]

theorem extendedPrimeLocalMap_flat [Module.Flat R S] :
    (Localization.localRingHom p P (algebraMap R S) hp).Flat :=
  (RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat R S)).localRingHom P p hp

theorem extendedPrimeLocalMap_ord [Module.Flat R S]
    (hP : p.map (algebraMap R S) = P) (a : Localization.AtPrime p) :
    Ring.ord (Localization.AtPrime P)
      (Localization.localRingHom p P (algebraMap R S) hp a) =
        Ring.ord (Localization.AtPrime p) a := by
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime P) :=
    (Localization.localRingHom p P (algebraMap R S) hp).toAlgebra
  let : Module.Flat (Localization.AtPrime p) (Localization.AtPrime P) :=
    extendedPrimeLocalMap_flat p P hp
  let : IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime P)) :=
    inferInstanceAs (IsLocalHom (Localization.localRingHom p P (algebraMap R S) hp))
  exact FlatOrderEq.BundleCycles.FlatOrder.ord_eq (Localization.AtPrime p) (Localization.AtPrime P)
    (extendedPrimeLocalMap_maximalIdeal p P hp hP) a

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.FlatExtendedPrimeOrder.BundleCycles
