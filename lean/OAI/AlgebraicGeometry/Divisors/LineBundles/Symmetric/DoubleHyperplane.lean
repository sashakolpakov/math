import OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.HyperplaneIdealIso
import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.Inclusion

/-! # Double Hyperplane -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.DoubleHyperplane.BundleCycles

noncomputable section

/-! The first two coordinates in a twice-augmented module give
two genuine isomorphic hyperplane ideals. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]

def augmentedCoordinateSwap : (R × (R × M)) ≃ₗ[R] R × (R × M) where
  toFun z := (z.2.1, (z.1, z.2.2))
  invFun z := (z.2.1, (z.1, z.2.2))
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem symmetricSplitHyperplane_refl :
    HyperplaneIdealIso.BundleCycles.symmetricSplitHyperplaneMap (LinearEquiv.refl R (R × M)) = SymmetricInfinity.Inclusion.BundleCycles.symmetricInfinityInclusion R M := by
  have h : SplitHyperplane.BundleCycles.splitHyperplaneQuotient (LinearEquiv.refl R (R × M)) = LinearMap.snd R R M := by
    apply LinearMap.ext
    intro z
    rfl
  exact SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveMap_congr h _ _

def symmetricSecondHyperplane :
    SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveScheme R (R × M) ⟶ SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveScheme R (R × (R × M)) :=
  HyperplaneIdealIso.BundleCycles.symmetricSplitHyperplaneMap (augmentedCoordinateSwap R M)

instance symmetricSecondHyperplane_isClosedImmersion : IsClosedImmersion (symmetricSecondHyperplane R M) :=
  inferInstanceAs (IsClosedImmersion (HyperplaneIdealIso.BundleCycles.symmetricSplitHyperplaneMap (augmentedCoordinateSwap R M)))

theorem symmetricSecondHyperplane_regular : Cartier.IdealBundle.Cycles.HasRegularPrincipalImageIdeals (symmetricSecondHyperplane R M) :=
  HyperplaneIdealIso.BundleCycles.symmetricSplitHyperplane_regular (augmentedCoordinateSwap R M)

def symmetricFirstSecondHyperplaneIdealIso :
    Scheme.SchemeIdealModule.BundleCycles.schemeIdealModule (SymmetricInfinity.Inclusion.BundleCycles.symmetricInfinityInclusion R (R × M)) ≅ Scheme.SchemeIdealModule.BundleCycles.schemeIdealModule (symmetricSecondHyperplane R M) :=
  eqToIso (congrArg Scheme.SchemeIdealModule.BundleCycles.schemeIdealModule (symmetricSplitHyperplane_refl R (R × M)).symm) ≪≫
    HyperplaneIdealIso.BundleCycles.symmetricSplitHyperplaneIdealIso (LinearEquiv.refl R (R × (R × M))) (augmentedCoordinateSwap R M)

theorem symmetricSecondHyperplane_equation_image :
    GradedMap.BundleCycles.symmetricGradedMap (LinearMap.snd R R (R × M)) (SplitHyperplane.BundleCycles.splitHyperplaneEquation (augmentedCoordinateSwap R M)) =
      Augmented.SymmetricChart.BundleCycles.augmentedSymmetricVariable R M := by
  exact GradedMap.BundleCycles.symmetricGradedMap_generator (LinearMap.snd R R (R × M)) ((augmentedCoordinateSwap R M).symm (1, 0))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.DoubleHyperplane.BundleCycles
