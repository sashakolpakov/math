import OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.ProperReciprocity
import OAI.AlgebraicGeometry.Divisors.LineBundles.Geometric.Steinberg

/-! # Rational Reciprocity -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.RationalReciprocity.BundleCycles

noncomputable section

/-!
# LineBundleCycles: actual local residue reciprocity for proper rational representatives

The two rational functions are the actual quotients of their affine
regular representatives. Bilinearity reduces the complete residue cycle
to the four numerator/denominator cross-intersections. Their proved
proper reciprocity makes the full cycle zero, including all poles.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R]
variable [IsLocalRing R] [IsIntegrallyClosed R]

theorem affineRationalResidueBoundary_zero (a c b d : R)
    (ha : a ≠ 0) (hc : c ≠ 0) (hb : b ≠ 0) (hd : d ≠ 0) (hdim : ringKrullDim R = 2)
    (hab : (Ideal.span {a, b}).radical = IsLocalRing.maximalIdeal R)
    (had : (Ideal.span {a, d}).radical = IsLocalRing.maximalIdeal R)
    (hcb : (Ideal.span {c, b}).radical = IsLocalRing.maximalIdeal R)
    (hcd : (Ideal.span {c, d}).radical = IsLocalRing.maximalIdeal R) :
    Normal.PointResidue.BundleCycles.normalResidueBoundaryCycle (Spec (CommRingCat.of R)) (ProperReciprocity.BundleCycles.affineNormal_stalk_integrallyClosed R)
      (ProperReciprocity.BundleCycles.affineFunctionUnit R a ha / ProperReciprocity.BundleCycles.affineFunctionUnit R c hc)
      (ProperReciprocity.BundleCycles.affineFunctionUnit R b hb / ProperReciprocity.BundleCycles.affineFunctionUnit R d hd) = 0 := by
  rw [Geometric.Steinberg.BundleCycles.normalResidueBoundaryCycle_div_left, Geometric.Steinberg.BundleCycles.normalResidueBoundaryCycle_div_right,
    Geometric.Steinberg.BundleCycles.normalResidueBoundaryCycle_div_right,
    ProperReciprocity.BundleCycles.affineProperResidueBoundary_zero R a b ha hb hdim hab,
    ProperReciprocity.BundleCycles.affineProperResidueBoundary_zero R a d ha hd hdim had,
    ProperReciprocity.BundleCycles.affineProperResidueBoundary_zero R c b hc hb hdim hcb,
    ProperReciprocity.BundleCycles.affineProperResidueBoundary_zero R c d hc hd hdim hcd]
  simp only [sub_zero]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.RationalReciprocity.BundleCycles
