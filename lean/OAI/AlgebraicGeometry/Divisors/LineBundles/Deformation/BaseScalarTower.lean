import OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.Localization

/-! # Base Scalar Tower -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.BaseScalarTower.BundleCycles

noncomputable section

/-! Coefficient extension on actual deformation algebras preserves
the scalar structure from any original base ring. -/

theorem deformationBaseMap_scalarTower (A R S : Type) [CommRing A] [CommRing R] [CommRing S]
    [Algebra A R] [Algebra A S] [Algebra R S] [IsScalarTower A R S] (I : Ideal R) :
    letI := (Localization.BundleCycles.deformationBaseMap I S).toAlgebra
    IsScalarTower A (Iff.BundleCycles.deformationAlgebra I) (Iff.BundleCycles.deformationAlgebra (I.map (algebraMap R S))) := by
  let := (Localization.BundleCycles.deformationBaseMap I S).toAlgebra
  apply IsScalarTower.of_algebraMap_eq
  intro a
  change algebraMap A (Iff.BundleCycles.deformationAlgebra (I.map (algebraMap R S))) a =
    Maps.BundleCycles.deformationMap I _ (algebraMap R S) Ideal.le_comap_map
      (algebraMap A (Iff.BundleCycles.deformationAlgebra I) a)
  rw [IsScalarTower.algebraMap_apply A R (Iff.BundleCycles.deformationAlgebra I), Maps.BundleCycles.deformationMap_algebraMap,
    ← IsScalarTower.algebraMap_apply A R S,
    ← IsScalarTower.algebraMap_apply A S (Iff.BundleCycles.deformationAlgebra (I.map (algebraMap R S)))]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.BaseScalarTower.BundleCycles
