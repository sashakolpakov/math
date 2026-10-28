import OAI.AlgebraicGeometry.Divisors.LineBundles.Geometric.AffinePrimeExtension
import OAI.AlgebraicGeometry.Divisors.LineBundles.FlatPrimeExtension
import OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.FiberFieldNaturality

/-! # Affine Prime Point -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Geometric.AffinePrimePoint.BundleCycles

noncomputable section

/-! Extended prime points of a smooth affine morphism with geometrically
integral fibers are its actual fiber generic points and preserve codimension. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [Smooth (AlgebraSpectrumProjection.BundleCycles.algebraSpectrumProjection R S)]
    [GeometricallyIntegral (AlgebraSpectrumProjection.BundleCycles.algebraSpectrumProjection R S)]

def geometricAffinePrimePoint (p : Spec (.of R)) : Spec (.of S) :=
  ⟨p.asIdeal.map (algebraMap R S), by
    let : p.asIdeal.IsPrime := (show PrimeSpectrum R from p).isPrime
    exact AffinePrimeExtension.BundleCycles.geometricAffine_primeExtension R S p.asIdeal⟩

theorem geometricAffinePrimePoint_projection (p : Spec (.of R)) :
    AlgebraSpectrumProjection.BundleCycles.algebraSpectrumProjection R S (geometricAffinePrimePoint R S p) = p :=
  PrimeSpectrum.ext (AlgebraSpectrumProjection.BundleCycles.algebraSpectrumProjection_comap_map R S p.asIdeal)

theorem geometricAffinePrimePoint_injective : Function.Injective (geometricAffinePrimePoint R S) :=
  Function.LeftInverse.injective (geometricAffinePrimePoint_projection R S)

theorem geometricAffinePrimePoint_specializes (P : Spec (.of S)) :
    geometricAffinePrimePoint R S (AlgebraSpectrumProjection.BundleCycles.algebraSpectrumProjection R S P) ⤳ P := by
  apply (PrimeSpectrum.le_iff_specializes _ _).mp
  exact Ideal.map_comap_le

theorem geometricAffinePrimePoint_eq_fiberGeneric (p : Spec (.of R)) :
    geometricAffinePrimePoint R S p = Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (AlgebraSpectrumProjection.BundleCycles.algebraSpectrumProjection R S) p := by
  apply Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint_unique _ _ _ (geometricAffinePrimePoint_projection R S p)
  intro P hP
  simpa only [hP] using geometricAffinePrimePoint_specializes R S P

theorem geometricAffinePrimePoint_coheight [IsNoetherianRing S] (p : Spec (.of R)) :
    Order.coheight (geometricAffinePrimePoint R S p) = Order.coheight p := by
  let : p.asIdeal.IsPrime := (show PrimeSpectrum R from p).isPrime
  let : (p.asIdeal.map (algebraMap R S)).IsPrime := AffinePrimeExtension.BundleCycles.geometricAffine_primeExtension R S p.asIdeal
  let : Module.Flat R S := RingHom.flat_algebraMap_iff.mp
    ((Flat.SpecMap_iff (f := CommRingCat.ofHom (algebraMap R S))).mp
      (inferInstanceAs (Flat (AlgebraSpectrumProjection.BundleCycles.algebraSpectrumProjection R S))))
  rw [← idealHeight_eq_coheight, ← idealHeight_eq_coheight]
  exact FlatPrimeExtension.BundleCycles.flatPrimeExtension_height p.asIdeal (AlgebraSpectrumProjection.BundleCycles.algebraSpectrumProjection_comap_map R S p.asIdeal)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Geometric.AffinePrimePoint.BundleCycles
