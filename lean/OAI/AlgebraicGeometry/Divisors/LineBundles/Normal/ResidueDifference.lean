import OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.ResidueCartier
import OAI.AlgebraicGeometry.Divisors.LineBundles.Geometric.ResidueLaws

/-! # Residue Difference -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.ResidueDifference.BundleCycles

noncomputable section

/-!
# LineBundleCycles: the residue divisor is the difference of the actual proper intersection terms

At a point where at least one regular equation is a local unit, the
normal residue principal divisor equals the difference of the two
native order-weighted Cartier cycles. The opposite term vanishes by
the actual unit-germ order theorem.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.Order

variable (X : Scheme) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
variable (x : X) (hx : coheight x = 1) [IsIntegrallyClosed (X.presheaf.stalk x)]

theorem normalPointResidueFunction_swap (g h : X.functionFieldˣ) :
    PointResidue.BundleCycles.normalPointResidueFunction X x hx h g = (PointResidue.BundleCycles.normalPointResidueFunction X x hx g h)⁻¹ := by
  let := PointResidue.BundleCycles.normal_stalk_isDVR X x hx
  let π := Classical.choose (IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk x))
  have hπ : Irreducible π := Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible _)
  have he := congrArg (Point.SupportResidue.BundleCycles.pointSupportResidueFunction X x) (DVRResidueRegularSteinberg.BundleCycles.dvrResidueQuotient_swap π hπ g h)
  refine he.trans ?_
  unfold Point.SupportResidue.BundleCycles.pointSupportResidueFunction
  rw [Units.val_inv_eq_inv_val]
  exact map_inv₀ (Point.SupportResidue.BundleCycles.pointSupportResidueIso X x).hom.hom _

theorem normalResidue_principal_swap (g h : X.functionFieldˣ) :
    Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor (irreducibleSetEquivPoints.symm x) (PointResidue.BundleCycles.normalPointResidueFunction X x hx h g) =
      -Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor (irreducibleSetEquivPoints.symm x) (PointResidue.BundleCycles.normalPointResidueFunction X x hx g h) := by
  rw [normalPointResidueFunction_swap]
  have he := Support.PrincipalLaws.BundleCycles.schemePrincipalPointDivisor_zpow (irreducibleSetEquivPoints.symm x)
    (Units.mk0 (PointResidue.BundleCycles.normalPointResidueFunction X x hx g h) (PointResidue.BundleCycles.normalPointResidueFunction_ne_zero X x hx g h)) (-1)
  simp only [Units.val_mk0, zpow_neg_one, neg_one_zsmul] at he
  exact he

theorem normalResidue_principal_proper (a b : Γ(X, ⊤))
    (hu : IsUnit (X.presheaf.germ ⊤ x (by trivial) a) ∨ IsUnit (X.presheaf.germ ⊤ x (by trivial) b))
    (g h : X.functionFieldˣ)
    (hg : (g : X.functionField) = RegularDivisor.BundleCycles.globalFunctionFieldElement X a)
    (hh : (h : X.functionField) = RegularDivisor.BundleCycles.globalFunctionFieldElement X b) :
    Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor (irreducibleSetEquivPoints.symm x) (PointResidue.BundleCycles.normalPointResidueFunction X x hx g h) =
      (X.ord (h : X.functionField) x : ℚ) • Principal.CartierCycle.BundleCycles.principalCartierPointCycle a (irreducibleSetEquivPoints.symm x) -
        (X.ord (g : X.functionField) x : ℚ) • Principal.CartierCycle.BundleCycles.principalCartierPointCycle b (irreducibleSetEquivPoints.symm x) := by
  rcases hu with ha | hb
  · have hz : X.ord (g : X.functionField) x = 0 :=
      (congrArg (fun t => X.ord t x) hg).trans (RegularDivisor.BundleCycles.regularFunctionDivisor_eq_zero_of_isUnit_germ X a x ha)
    rw [ResidueCartier.BundleCycles.normalResidue_principal_regularUnit_rat X x hx a ha g h hg, hz, Int.cast_zero, zero_smul, sub_zero]
  · have hz : X.ord (h : X.functionField) x = 0 :=
      (congrArg (fun t => X.ord t x) hh).trans (RegularDivisor.BundleCycles.regularFunctionDivisor_eq_zero_of_isUnit_germ X b x hb)
    rw [normalResidue_principal_swap X x hx h g,
      ResidueCartier.BundleCycles.normalResidue_principal_regularUnit_rat X x hx b hb h g hh, hz, Int.cast_zero, zero_smul, zero_sub]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.ResidueDifference.BundleCycles
