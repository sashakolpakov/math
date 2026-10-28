import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.Bundle
import OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.IdealPullbackIso

/-! # Equiv -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.Equiv.BundleCycles

noncomputable section

/-! A change of module coordinates preserves the actual infinity
Cartier ideal through its genuine projective pullback square. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N)

def augmentedLinearEquiv : (R × M) ≃ₗ[R] R × N := (LinearEquiv.refl R R).prodCongr e

theorem symmetricInfinity_linearEquiv_square :
    Inclusion.BundleCycles.symmetricInfinityInclusion R N ≫ (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveIso (augmentedLinearEquiv e)).inv =
      (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveIso e).inv ≫ Inclusion.BundleCycles.symmetricInfinityInclusion R M := by
  have h : (LinearMap.snd R R N).comp (augmentedLinearEquiv e).toLinearMap =
      e.toLinearMap.comp (LinearMap.snd R R M) := by
    apply LinearMap.ext
    intro z
    rfl
  exact (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveMap_comp (augmentedLinearEquiv e).toLinearMap (augmentedLinearEquiv e).surjective
    (LinearMap.snd R R N) (fun n => ⟨(0, n), rfl⟩)).symm.trans
    ((SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveMap_congr h _ _).trans
      (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveMap_comp (LinearMap.snd R R M) (fun m => ⟨(0, m), rfl⟩) e.toLinearMap e.surjective))

theorem symmetricInfinity_linearEquiv_isPullback :
    IsPullback (Inclusion.BundleCycles.symmetricInfinityInclusion R N) (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveIso e).inv
      (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveIso (augmentedLinearEquiv e)).inv (Inclusion.BundleCycles.symmetricInfinityInclusion R M) :=
  IsPullback.of_vert_isIso ⟨symmetricInfinity_linearEquiv_square e⟩

def symmetricInfinity_linearEquiv_idealIso :
    ((Bundle.Cycles.symmetricInfinityIdealLineBundle R M).pullback (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveIso (augmentedLinearEquiv e)).inv).sheaf ≅
      (Bundle.Cycles.symmetricInfinityIdealLineBundle R N).sheaf :=
  Cartier.IdealPullbackIso.BundleCycles.cartierIdealPullbackIso (Inclusion.BundleCycles.symmetricInfinityInclusion R M) (Inclusion.BundleCycles.symmetricInfinityInclusion R N)
    (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveIso (augmentedLinearEquiv e)).inv (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveIso e).inv
    (symmetricInfinity_linearEquiv_isPullback e)
    (Bundle.Cycles.symmetricInfinity_regularPrincipalImageIdeals R M) (Bundle.Cycles.symmetricInfinity_regularPrincipalImageIdeals R N)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.Equiv.BundleCycles
