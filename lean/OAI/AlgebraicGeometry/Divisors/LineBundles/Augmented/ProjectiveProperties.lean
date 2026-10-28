import OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.ProjectiveLocalProperty
import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.IntegralFibers

/-! # Projective Properties -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.ProjectiveProperties.BundleCycles

noncomputable section

/-! The actual projective compactification of a finite projective
module is smooth with geometrically integral fibers. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {R : Type} [CommRing R] (M : Type) [AddCommGroup M] [Module R M]
    [Module.Projective R M] [Module.Finite R M]

instance symmetricAugmentedProjective_geometricallyIntegral :
    GeometricallyIntegral (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M)) :=
  ProjectiveLocalProperty.BundleCycles.augmentedProjective_property M (@GeometricallyIntegral)
    (fun _S _N _κ _ _ _ _ _ b => SymmetricProjective.IntegralFibers.BundleCycles.symmetricProjective_geometricallyIntegral b)

instance symmetricAugmentedProjective_smooth : Smooth (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M)) := by
  let : IsZariskiLocalAtTarget (@Smooth.{0}) := HasRingHomProperty.instIsZariskiLocalAtTarget _
  exact ProjectiveLocalProperty.BundleCycles.augmentedProjective_property M (@Smooth)
    (fun _S _N _κ _ _ _ _ _ b => (Symmetric.BasisAffineChart.BundleCycles.symmetricProjective_hasAffineSpaceSourceCharts b).smooth)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.ProjectiveProperties.BundleCycles
