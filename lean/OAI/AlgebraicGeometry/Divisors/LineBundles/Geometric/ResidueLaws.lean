import OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.PointResidue

/-! # Residue Laws -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Geometric.ResidueLaws.BundleCycles

noncomputable section

/-!
# LineBundleCycles: product laws for the actual geometric residue functions

The residue-field/function-field isomorphism preserves multiplication.
Thus the proved local residue quotient laws give product laws for the
actual rational functions on the reduced point closures.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace _root_.Order

variable (X : Scheme) (x : X)

theorem pointSupportResidueFunction_mul (r s : (X.residueField x)ˣ) :
    Point.SupportResidue.BundleCycles.pointSupportResidueFunction X x (r * s) =
      Point.SupportResidue.BundleCycles.pointSupportResidueFunction X x r * Point.SupportResidue.BundleCycles.pointSupportResidueFunction X x s :=
  map_mul (Point.SupportResidue.BundleCycles.pointSupportResidueIso X x).hom.hom (r : X.residueField x) (s : X.residueField x)

theorem pointSupportResidueFunction_one : Point.SupportResidue.BundleCycles.pointSupportResidueFunction X x 1 = 1 :=
  map_one (Point.SupportResidue.BundleCycles.pointSupportResidueIso X x).hom.hom

variable [IsIntegral X]

section DVR

variable [IsDiscreteValuationRing (X.presheaf.stalk x)] (π : X.presheaf.stalk x) (hπ : Irreducible π)

theorem geometricResidueFunction_mul_left (g h k : X.functionFieldˣ) :
    ResidueFunction.BundleCycles.geometricResidueFunction X x π hπ (g * h) k =
      ResidueFunction.BundleCycles.geometricResidueFunction X x π hπ g k * ResidueFunction.BundleCycles.geometricResidueFunction X x π hπ h k :=
  (congrArg (Point.SupportResidue.BundleCycles.pointSupportResidueFunction X x) (DVRResidueRegularSteinberg.BundleCycles.dvrResidueQuotient_mul_left π hπ g h k)).trans
    (pointSupportResidueFunction_mul X x _ _)

theorem geometricResidueFunction_mul_right (g h k : X.functionFieldˣ) :
    ResidueFunction.BundleCycles.geometricResidueFunction X x π hπ g (h * k) =
      ResidueFunction.BundleCycles.geometricResidueFunction X x π hπ g h * ResidueFunction.BundleCycles.geometricResidueFunction X x π hπ g k :=
  (congrArg (Point.SupportResidue.BundleCycles.pointSupportResidueFunction X x) (DVRResidueRegularSteinberg.BundleCycles.dvrResidueQuotient_mul_right π hπ g h k)).trans
    (pointSupportResidueFunction_mul X x _ _)

theorem geometricResidueFunction_zero_orders (g h : X.functionFieldˣ)
    (hg : SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder (X.presheaf.stalk x) (g : X.functionField) = 0)
    (hh : SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder (X.presheaf.stalk x) (h : X.functionField) = 0) :
    ResidueFunction.BundleCycles.geometricResidueFunction X x π hπ g h = 1 := by
  have he : DVRResidueOf.BundleCycles.dvrResidueQuotient π hπ g h = 1 := by
    unfold DVRResidueOf.BundleCycles.dvrResidueQuotient DVRResidueOf.BundleCycles.dvrBalancedUnit
    rw [hg, hh, zpow_zero, zpow_zero, div_one, map_one]
  exact (congrArg (Point.SupportResidue.BundleCycles.pointSupportResidueFunction X x) he).trans (pointSupportResidueFunction_one X x)

end DVR

variable [AlgebraicGeometry.IsNoetherian X]
variable (hx : coheight x = 1) [IsIntegrallyClosed (X.presheaf.stalk x)]

theorem normalPointResidueFunction_mul_left (g h k : X.functionFieldˣ) :
    Normal.PointResidue.BundleCycles.normalPointResidueFunction X x hx (g * h) k =
      Normal.PointResidue.BundleCycles.normalPointResidueFunction X x hx g k * Normal.PointResidue.BundleCycles.normalPointResidueFunction X x hx h k := by
  let := Normal.PointResidue.BundleCycles.normal_stalk_isDVR X x hx
  exact geometricResidueFunction_mul_left X x _ _ g h k

theorem normalPointResidueFunction_mul_right (g h k : X.functionFieldˣ) :
    Normal.PointResidue.BundleCycles.normalPointResidueFunction X x hx g (h * k) =
      Normal.PointResidue.BundleCycles.normalPointResidueFunction X x hx g h * Normal.PointResidue.BundleCycles.normalPointResidueFunction X x hx g k := by
  let := Normal.PointResidue.BundleCycles.normal_stalk_isDVR X x hx
  exact geometricResidueFunction_mul_right X x _ _ g h k

theorem normalPointResidueFunction_zero_orders (g h : X.functionFieldˣ)
    (hg : X.ord (g : X.functionField) x = 0) (hh : X.ord (h : X.functionField) x = 0) :
    Normal.PointResidue.BundleCycles.normalPointResidueFunction X x hx g h = 1 := by
  let := Normal.PointResidue.BundleCycles.normal_stalk_isDVR X x hx
  apply geometricResidueFunction_zero_orders
  · exact (X.ord_eq_ordHom_of_coheight_eq_one hx _).symm.trans hg
  · exact (X.ord_eq_ordHom_of_coheight_eq_one hx _).symm.trans hh

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Geometric.ResidueLaws.BundleCycles
