import OAI.AlgebraicGeometry.Divisors.LineBundles.RationalNormalUnitRestriction
import OAI.AlgebraicGeometry.Divisors.LineBundles.Support.PrincipalLaws

/-! # Rational Restriction Residue -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.RationalRestrictionResidue.BundleCycles

noncomputable section

/-! # LineBundleCycles: proper residue-symbol terms are the actual restricted rational functions and their divisors -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace _root_.Order

variable (X : Scheme.{0}) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
    (x : X) (hx : coheight x = 1) [IsIntegrallyClosed (X.presheaf.stalk x)]

theorem normalPointResidueFunction_of_order_zero (g h : X.functionFieldˣ) (hg : X.ord g.val x = 0) :
    PointResidue.BundleCycles.normalPointResidueFunction X x hx g h =
      (RationalNormalUnitRestriction.BundleCycles.normalRationalRestriction X x hx g hg).val ^ X.ord h.val x := by
  let := PointResidue.BundleCycles.normal_stalk_isDVR X x hx
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk x)
  rw [PointResidue.BundleCycles.normalPointResidueFunction_eq X x hx π hπ]
  have hu := RationalNormalUnitRestriction.BundleCycles.normalOrderZeroUnit_spec X x hx g hg
  calc
    Geometric.ResidueFunction.BundleCycles.geometricResidueFunction X x π hπ g h =
        Geometric.ResidueFunction.BundleCycles.geometricResidueFunction X x π hπ
          (Units.map (algebraMap (X.presheaf.stalk x) X.functionField).toMonoidHom
            (RationalNormalUnitRestriction.BundleCycles.normalOrderZeroUnit X x hx g hg)) h :=
      congrArg (fun v => Geometric.ResidueFunction.BundleCycles.geometricResidueFunction X x π hπ v h) hu.symm
    _ = (RationalNormalUnitRestriction.BundleCycles.normalRationalRestriction X x hx g hg).val ^ SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder (X.presheaf.stalk x) h.val := by
      unfold Geometric.ResidueFunction.BundleCycles.geometricResidueFunction
      rw [DVRResidueRegularSteinberg.BundleCycles.dvrResidueQuotient_localUnit]
      change (Point.SupportResidue.BundleCycles.pointSupportResidueIso X x).hom
        (((Units.map (IsLocalRing.residue (X.presheaf.stalk x)).toMonoidHom
          (RationalNormalUnitRestriction.BundleCycles.normalOrderZeroUnit X x hx g hg)) ^ SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder (X.presheaf.stalk x) h.val).val) = _
      rw [Units.val_zpow_eq_zpow_val]
      exact map_zpow₀ (Point.SupportResidue.BundleCycles.pointSupportResidueIso X x).hom.hom
        ((Units.map (IsLocalRing.residue (X.presheaf.stalk x)).toMonoidHom
          (RationalNormalUnitRestriction.BundleCycles.normalOrderZeroUnit X x hx g hg)).val : X.residueField x)
        (SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder (X.presheaf.stalk x) h.val)
    _ = _ := congrArg (fun n : ℤ => (RationalNormalUnitRestriction.BundleCycles.normalRationalRestriction X x hx g hg).val ^ n)
      (X.ord_eq_ordHom_of_coheight_eq_one hx h.val).symm

theorem normalResidue_principal_order_zero (g h : X.functionFieldˣ) (hg : X.ord g.val x = 0) :
    Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor (irreducibleSetEquivPoints.symm x) (PointResidue.BundleCycles.normalPointResidueFunction X x hx g h) =
      X.ord h.val x • Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor (irreducibleSetEquivPoints.symm x)
        (RationalNormalUnitRestriction.BundleCycles.normalRationalRestriction X x hx g hg).val := by
  rw [normalPointResidueFunction_of_order_zero X x hx g h hg]
  exact Support.PrincipalLaws.BundleCycles.schemePrincipalPointDivisor_zpow (irreducibleSetEquivPoints.symm x)
    (RationalNormalUnitRestriction.BundleCycles.normalRationalRestriction X x hx g hg) (X.ord h.val x)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.RationalRestrictionResidue.BundleCycles
