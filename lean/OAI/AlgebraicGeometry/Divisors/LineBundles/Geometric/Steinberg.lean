import OAI.AlgebraicGeometry.Divisors.LineBundles.DVRResidueRegularSteinberg
import OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.DivisorSign
import OAI.AlgebraicGeometry.Divisors.LineBundles.ResidueBoundaryAddition

/-! # Steinberg -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Geometric.Steinberg.BundleCycles

noncomputable section

section

/-!
# LineBundleCycles: the geometric residue boundary satisfies the Steinberg relation

For nonzero rational functions adding to one, each residue function is
one or a constant sign. Its actual principal divisor is zero. Thus the
complete finite geometric residue boundary vanishes as a cycle.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace _root_.Order

variable (X : Scheme) (x : X)

theorem pointSupportResidueFunction_sign (n : ℤ) :
    Point.SupportResidue.BundleCycles.pointSupportResidueFunction X x
      ((Units.map (IsLocalRing.residue (X.presheaf.stalk x)).toMonoidHom (-1 : (X.presheaf.stalk x)ˣ)) ^ n) =
        (-1 : (CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm x)).functionField) ^ n := by
  have hs : ((Units.map (IsLocalRing.residue (X.presheaf.stalk x)).toMonoidHom
      (-1 : (X.presheaf.stalk x)ˣ) : (IsLocalRing.ResidueField (X.presheaf.stalk x))ˣ) :
        IsLocalRing.ResidueField (X.presheaf.stalk x)) = -1 := by
    change IsLocalRing.residue (X.presheaf.stalk x) (-1) = -1
    rw [map_neg, map_one]
  unfold Point.SupportResidue.BundleCycles.pointSupportResidueFunction
  rw [Units.val_zpow_eq_zpow_val, hs]
  exact (map_zpow₀ (Point.SupportResidue.BundleCycles.pointSupportResidueIso X x).hom.hom (-1 : X.residueField x) n).trans
    (congrArg (fun z => z ^ n)
      ((map_neg (Point.SupportResidue.BundleCycles.pointSupportResidueIso X x).hom.hom 1).trans (congrArg Neg.neg (map_one _))))

variable [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]

theorem geometricResidueFunction_principal_add_one
    [IsDiscreteValuationRing (X.presheaf.stalk x)] (π : X.presheaf.stalk x) (hπ : Irreducible π)
    (g h : X.functionFieldˣ) (hsum : (g : X.functionField) + (h : X.functionField) = 1) :
    Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor (irreducibleSetEquivPoints.symm x)
      (ResidueFunction.BundleCycles.geometricResidueFunction X x π hπ g h) = 0 := by
  unfold ResidueFunction.BundleCycles.geometricResidueFunction
  by_cases hg : SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder (X.presheaf.stalk x) (g : X.functionField) < 0
  · rw [DVRResidueRegularSteinberg.BundleCycles.dvrResidueQuotient_add_one_of_neg π hπ g h hsum hg,
      pointSupportResidueFunction_sign, Principal.DivisorSign.BundleCycles.schemePrincipalPointDivisor_sign]
  · rw [DVRResidueRegularSteinberg.BundleCycles.dvrResidueQuotient_add_one_of_nonneg π hπ g h hsum (le_of_not_gt hg)]
    exact (congrArg (Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor (irreducibleSetEquivPoints.symm x))
      (ResidueLaws.BundleCycles.pointSupportResidueFunction_one X x)).trans (Support.PrincipalLaws.BundleCycles.schemePrincipalPointDivisor_one _)

theorem normalPointResidueFunction_principal_add_one (hx : coheight x = 1)
    [IsIntegrallyClosed (X.presheaf.stalk x)] (g h : X.functionFieldˣ)
    (hsum : (g : X.functionField) + (h : X.functionField) = 1) :
    Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor (irreducibleSetEquivPoints.symm x)
      (Normal.PointResidue.BundleCycles.normalPointResidueFunction X x hx g h) = 0 := by
  let := Normal.PointResidue.BundleCycles.normal_stalk_isDVR X x hx
  exact geometricResidueFunction_principal_add_one X x _ _ g h hsum

theorem normalResidueBoundaryCycle_add_one
    (hNormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) (g h : X.functionFieldˣ)
    (hsum : (g : X.functionField) + (h : X.functionField) = 1) :
    Normal.PointResidue.BundleCycles.normalResidueBoundaryCycle X hNormal g h = 0 := by
  unfold Normal.PointResidue.BundleCycles.normalResidueBoundaryCycle
  apply Finset.sum_eq_zero
  intro x _
  let := hNormal x
  exact normalPointResidueFunction_principal_add_one X x (Normal.PointResidue.BundleCycles.residueDivisorSupport_coheight X g h x) g h hsum

end

/-!
# LineBundleCycles: exchanging a residue pair through its actual sum

Bilinearity and the proved geometric Steinberg relation identify the
boundary of (g,h) with the sum of the boundaries of (g,g+h) and (g+h,h).
All expressions are the existing finite cycles on actual supports.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (X : Scheme) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
variable (hNormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))

theorem normalResidueBoundaryCycle_one_right (g : X.functionFieldˣ) :
    Normal.PointResidue.BundleCycles.normalResidueBoundaryCycle X hNormal g 1 = 0 := by
  rw [ResidueBoundaryAddition.BundleCycles.normalResidueBoundaryCycle_swap, ResidueBoundaryAddition.BundleCycles.normalResidueBoundaryCycle_one_left, neg_zero]

theorem normalResidueBoundaryCycle_inv_right (g h : X.functionFieldˣ) :
    Normal.PointResidue.BundleCycles.normalResidueBoundaryCycle X hNormal g h⁻¹ = -Normal.PointResidue.BundleCycles.normalResidueBoundaryCycle X hNormal g h := by
  have he := ResidueBoundaryAddition.BundleCycles.normalResidueBoundaryCycle_mul_right X hNormal g h h⁻¹
  rw [mul_inv_cancel, normalResidueBoundaryCycle_one_right] at he
  exact eq_neg_iff_add_eq_zero.mpr ((add_comm _ _).trans he.symm)

theorem normalResidueBoundaryCycle_div_left (g h k : X.functionFieldˣ) :
    Normal.PointResidue.BundleCycles.normalResidueBoundaryCycle X hNormal (g / h) k =
      Normal.PointResidue.BundleCycles.normalResidueBoundaryCycle X hNormal g k - Normal.PointResidue.BundleCycles.normalResidueBoundaryCycle X hNormal h k := by
  rw [div_eq_mul_inv, ResidueBoundaryAddition.BundleCycles.normalResidueBoundaryCycle_mul_left,
    ResidueBoundaryAddition.BundleCycles.normalResidueBoundaryCycle_inv_left, sub_eq_add_neg]

theorem normalResidueBoundaryCycle_div_right (g h k : X.functionFieldˣ) :
    Normal.PointResidue.BundleCycles.normalResidueBoundaryCycle X hNormal g (h / k) =
      Normal.PointResidue.BundleCycles.normalResidueBoundaryCycle X hNormal g h - Normal.PointResidue.BundleCycles.normalResidueBoundaryCycle X hNormal g k := by
  rw [div_eq_mul_inv, ResidueBoundaryAddition.BundleCycles.normalResidueBoundaryCycle_mul_right,
    normalResidueBoundaryCycle_inv_right, sub_eq_add_neg]

theorem normalResidueBoundaryCycle_exchange (g h s : X.functionFieldˣ)
    (hs : (g : X.functionField) + (h : X.functionField) = s) :
    Normal.PointResidue.BundleCycles.normalResidueBoundaryCycle X hNormal g h =
      Normal.PointResidue.BundleCycles.normalResidueBoundaryCycle X hNormal g s + Normal.PointResidue.BundleCycles.normalResidueBoundaryCycle X hNormal s h := by
  have hsum : ((g / s : X.functionFieldˣ) : X.functionField) +
      ((h / s : X.functionFieldˣ) : X.functionField) = 1 := by
    rw [Units.val_div_eq_div_val, Units.val_div_eq_div_val, ← add_div, hs, div_self s.ne_zero]
  have he := normalResidueBoundaryCycle_add_one X hNormal (g / s) (h / s) hsum
  rw [normalResidueBoundaryCycle_div_left, normalResidueBoundaryCycle_div_right,
    normalResidueBoundaryCycle_div_right, ResidueBoundaryAddition.BundleCycles.normalResidueBoundaryCycle_self, sub_zero] at he
  apply sub_eq_zero.mp
  exact (show Normal.PointResidue.BundleCycles.normalResidueBoundaryCycle X hNormal g h -
      (Normal.PointResidue.BundleCycles.normalResidueBoundaryCycle X hNormal g s + Normal.PointResidue.BundleCycles.normalResidueBoundaryCycle X hNormal s h) =
      (Normal.PointResidue.BundleCycles.normalResidueBoundaryCycle X hNormal g h - Normal.PointResidue.BundleCycles.normalResidueBoundaryCycle X hNormal g s) -
        Normal.PointResidue.BundleCycles.normalResidueBoundaryCycle X hNormal s h by abel).trans he

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Geometric.Steinberg.BundleCycles
