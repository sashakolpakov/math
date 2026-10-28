import OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.ClosedSupport

/-! # Map Injective -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.MapInjective.BundleCycles

noncomputable section

/-! Injective coefficient maps remain injective on the actual deformation algebra. -/

theorem deformationMap_injective {R S : Type} [CommRing R] [CommRing S]
    (I : Ideal R) (J : Ideal S) (f : R →+* S) (hf : I ≤ J.comap f)
    (hinj : Function.Injective f) : Function.Injective (Maps.BundleCycles.deformationMap I J f hf) := by
  intro a b hab
  apply Subtype.ext
  ext n
  apply hinj
  have h := congrArg (fun c : Iff.BundleCycles.deformationAlgebra J => c.val.coeff n) hab
  simpa only [Maps.BundleCycles.deformationMap_coeff] using h

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.MapInjective.BundleCycles
