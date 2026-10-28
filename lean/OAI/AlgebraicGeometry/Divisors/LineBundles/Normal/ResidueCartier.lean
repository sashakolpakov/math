import OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.PointResidue
import OAI.AlgebraicGeometry.Divisors.LineBundles.Support.PrincipalLaws
import OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.CartierCycle

/-! # Residue Cartier -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.ResidueCartier.BundleCycles

noncomputable section

/-!
# LineBundleCycles: proper-component residue divisors are actual Cartier intersection terms

When an ambient regular equation is a unit at the divisor point, its
normal residue function is its actual support restriction raised to the
other function's native order. Taking the complete principal divisor
gives that order times the actual Cartier intersection cycle.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.Order

variable (X : Scheme) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
variable (x : X) (hx : coheight x = 1) [IsIntegrallyClosed (X.presheaf.stalk x)]

theorem normalPointResidueFunction_regularUnit (a : Γ(X, ⊤))
    (ha : IsUnit (X.presheaf.germ ⊤ x (by trivial) a)) (g h : X.functionFieldˣ)
    (hg : (g : X.functionField) = RegularDivisor.BundleCycles.globalFunctionFieldElement X a) :
    PointResidue.BundleCycles.normalPointResidueFunction X x hx g h =
      (Principal.CartierCycle.BundleCycles.supportRegularFunction a (irreducibleSetEquivPoints.symm x)) ^ X.ord (h : X.functionField) x := by
  let := PointResidue.BundleCycles.normal_stalk_isDVR X x hx
  obtain ⟨u, hu⟩ := ha
  have hgu : g = Units.map (algebraMap (X.presheaf.stalk x) X.functionField).toMonoidHom u := by
    apply Units.ext
    change (g : X.functionField) = algebraMap (X.presheaf.stalk x) X.functionField (u : X.presheaf.stalk x)
    rw [hu]
    exact hg.trans (Scheme.algebraMap_germ_eq_germToFunctionField X (by trivial) a).symm
  rw [hgu]
  exact Geometric.ResidueRegular.BundleCycles.geometricResidueFunction_regular X x _ _ hx a u hu h

theorem normalResidue_principal_regularUnit (a : Γ(X, ⊤))
    (ha : IsUnit (X.presheaf.germ ⊤ x (by trivial) a)) (g h : X.functionFieldˣ)
    (hg : (g : X.functionField) = RegularDivisor.BundleCycles.globalFunctionFieldElement X a) :
    Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor (irreducibleSetEquivPoints.symm x) (PointResidue.BundleCycles.normalPointResidueFunction X x hx g h) =
      X.ord (h : X.functionField) x • Principal.CartierCycle.BundleCycles.principalCartierPointCycle a (irreducibleSetEquivPoints.symm x) := by
  obtain ⟨u, hu⟩ := ha
  have hn : Principal.CartierCycle.BundleCycles.supportRegularFunction a (irreducibleSetEquivPoints.symm x) ≠ 0 := by
    have he := Geometric.ResidueRegular.BundleCycles.pointSupportResidueFunction_regular X x a u hu
    intro hz
    exact Point.SupportResidue.BundleCycles.pointSupportResidueFunction_ne_zero X x
      (Units.map (IsLocalRing.residue (X.presheaf.stalk x)).toMonoidHom u) (he.trans hz)
  rw [normalPointResidueFunction_regularUnit X x hx a ⟨u, hu⟩ g h hg]
  exact Support.PrincipalLaws.BundleCycles.schemePrincipalPointDivisor_zpow (irreducibleSetEquivPoints.symm x)
    (Units.mk0 (Principal.CartierCycle.BundleCycles.supportRegularFunction a (irreducibleSetEquivPoints.symm x)) hn)
    (X.ord (h : X.functionField) x)

theorem normalResidue_principal_regularUnit_rat (a : Γ(X, ⊤))
    (ha : IsUnit (X.presheaf.germ ⊤ x (by trivial) a)) (g h : X.functionFieldˣ)
    (hg : (g : X.functionField) = RegularDivisor.BundleCycles.globalFunctionFieldElement X a) :
    Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor (irreducibleSetEquivPoints.symm x) (PointResidue.BundleCycles.normalPointResidueFunction X x hx g h) =
      (X.ord (h : X.functionField) x : ℚ) • Principal.CartierCycle.BundleCycles.principalCartierPointCycle a (irreducibleSetEquivPoints.symm x) := by
  rw [Int.cast_smul_eq_zsmul]
  exact normalResidue_principal_regularUnit X x hx a ha g h hg

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.ResidueCartier.BundleCycles
