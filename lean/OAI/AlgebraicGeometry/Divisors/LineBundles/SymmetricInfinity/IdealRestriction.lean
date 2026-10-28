import OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.HyperplaneIntersection
import OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.IdealPullbackIso
import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.Bundle

/-! # Ideal Restriction -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.IdealRestriction.BundleCycles

noncomputable section

/-! The actual infinity ideal line bundle restricts to the
infinity ideal line bundle in one lower projective dimension. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

def symmetricInfinityIdealRestrictionIso (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] :
    ((Bundle.Cycles.symmetricInfinityIdealLineBundle R (R × M)).pullback (Inclusion.BundleCycles.symmetricInfinityInclusion R (R × M))).sheaf ≅
      (Bundle.Cycles.symmetricInfinityIdealLineBundle R M).sheaf :=
  (Scheme.Modules.pullback (Inclusion.BundleCycles.symmetricInfinityInclusion R (R × M))).mapIso
    (Symmetric.DoubleHyperplane.BundleCycles.symmetricFirstSecondHyperplaneIdealIso R M) ≪≫
  Cartier.IdealPullbackIso.BundleCycles.cartierIdealPullbackIso (Symmetric.DoubleHyperplane.BundleCycles.symmetricSecondHyperplane R M) (Inclusion.BundleCycles.symmetricInfinityInclusion R M)
    (Inclusion.BundleCycles.symmetricInfinityInclusion R (R × M)) (Inclusion.BundleCycles.symmetricInfinityInclusion R M)
    (Symmetric.HyperplaneIntersection.BundleCycles.symmetricHyperplanes_isPullback R M) (Symmetric.DoubleHyperplane.BundleCycles.symmetricSecondHyperplane_regular R M)
    (Bundle.Cycles.symmetricInfinity_regularPrincipalImageIdeals R M)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.IdealRestriction.BundleCycles
