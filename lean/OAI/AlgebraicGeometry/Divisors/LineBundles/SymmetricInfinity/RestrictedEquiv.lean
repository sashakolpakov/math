import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.Equiv
import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.IdealRestriction
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.PullbackIso

/-! # Restricted Equiv -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.RestrictedEquiv.BundleCycles

noncomputable section

/-! The actual infinity ideal restricted to the hyperplane is
preserved by module coordinates and becomes the smaller infinity ideal
after a genuine splitting of one coordinate. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

def symmetricInfinityRestriction_linearEquivIso (e : M ≃ₗ[R] N) :
    (((Bundle.Cycles.symmetricInfinityIdealLineBundle R M).pullback (Inclusion.BundleCycles.symmetricInfinityInclusion R M)).pullback
      (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveIso e).inv).sheaf ≅
      ((Bundle.Cycles.symmetricInfinityIdealLineBundle R N).pullback (Inclusion.BundleCycles.symmetricInfinityInclusion R N)).sheaf :=
  (LineBundle.PullbackIso.Cycles.lineBundlePullbackSquareIso (Bundle.Cycles.symmetricInfinityIdealLineBundle R M)
    ((Bundle.Cycles.symmetricInfinityIdealLineBundle R M).pullback (Inclusion.BundleCycles.symmetricInfinityInclusion R M))
    (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveIso (Equiv.BundleCycles.augmentedLinearEquiv e)).inv (Inclusion.BundleCycles.symmetricInfinityInclusion R M)
    (Inclusion.BundleCycles.symmetricInfinityInclusion R N) (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveIso e).inv
    (Equiv.BundleCycles.symmetricInfinity_linearEquiv_square e) (Iso.refl _)).symm ≪≫
      LineBundle.PullbackIso.Cycles.lineBundlePullbackIso (Equiv.BundleCycles.symmetricInfinity_linearEquiv_idealIso e) (Inclusion.BundleCycles.symmetricInfinityInclusion R N)

def symmetricInfinityRestriction_splitIso (e : M ≃ₗ[R] R × N) :
    (((Bundle.Cycles.symmetricInfinityIdealLineBundle R M).pullback (Inclusion.BundleCycles.symmetricInfinityInclusion R M)).pullback
      (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveIso e).inv).sheaf ≅ (Bundle.Cycles.symmetricInfinityIdealLineBundle R N).sheaf :=
  symmetricInfinityRestriction_linearEquivIso e ≪≫ IdealRestriction.BundleCycles.symmetricInfinityIdealRestrictionIso R N

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.RestrictedEquiv.BundleCycles
