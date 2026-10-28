import OAI.AlgebraicGeometry.Divisors.LineBundles.AlgebraSpectrumProjection
import OAI.AlgebraicGeometry.Divisors.LineBundles.QuotientFiber
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # Affine Prime Extension -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Geometric.AffinePrimeExtension.BundleCycles

noncomputable section

/-! A smooth affine projection with geometrically integral fibers
extends every base prime to a prime ideal. This follows from the actual
quotient pullback over the corresponding integral closed base. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [Smooth (AlgebraSpectrumProjection.BundleCycles.algebraSpectrumProjection R S)]
    [GeometricallyIntegral (AlgebraSpectrumProjection.BundleCycles.algebraSpectrumProjection R S)]

theorem geometricAffine_primeExtension (p : Ideal R) [p.IsPrime] :
    (p.map (algebraMap R S)).IsPrime := by
  let φ : CommRingCat.of R ⟶ CommRingCat.of S := CommRingCat.ofHom (algebraMap R S)
  let ψ : CommRingCat.of (R ⧸ p) ⟶ CommRingCat.of (S ⧸ p.map (algebraMap R S)) :=
    CommRingCat.ofHom (Ideal.quotientMap (p.map (algebraMap R S)) (algebraMap R S)
      (fun _ hx => Ideal.mem_map_of_mem _ hx))
  have hs : IsPullback
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (p.map (algebraMap R S)))))
      (Spec.map ψ) (AlgebraSpectrumProjection.BundleCycles.algebraSpectrumProjection R S) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk p))) := by
    apply AlgebraicGeometry.isPullback_SpecMap_of_isPushout
    exact QuotientFiber.BundleCycles.quotient_isPushout φ p
  let : Smooth (Spec.map ψ) := MorphismProperty.of_isPullback hs inferInstance
  let : GeometricallyIntegral (Spec.map ψ) := MorphismProperty.of_isPullback hs inferInstance
  let : IsIntegral (Spec (.of (S ⧸ p.map (algebraMap R S)))) :=
    GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (Spec.map ψ)
  let : IsDomain (S ⧸ p.map (algebraMap R S)) :=
    (affine_isIntegral_iff (.of (S ⧸ p.map (algebraMap R S)))).mp inferInstance
  exact (Ideal.Quotient.isDomain_iff_prime (p.map (algebraMap R S))).mp inferInstance

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Geometric.AffinePrimeExtension.BundleCycles
