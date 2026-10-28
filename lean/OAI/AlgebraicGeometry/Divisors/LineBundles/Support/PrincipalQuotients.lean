import OAI.AlgebraicGeometry.Divisors.LineBundles.Support.PrincipalLaws
import OAI.AlgebraicGeometry.Divisors.LineBundles.Geometric.FactoredResidue

/-! # Principal Quotients -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Support.PrincipalQuotients.BundleCycles

noncomputable section

/-! # LineBundleCycles: complete principal divisors of quotient powers -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X : Scheme} [AlgebraicGeometry.IsNoetherian X] (W : IrreducibleCloseds X)

theorem schemePrincipalPointDivisor_div (g h : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField)
    (hg : g ≠ 0) (hh : h ≠ 0) :
    Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W (g / h) =
      Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W g - Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W h := by
  have he := congrArg Multiplicative.toAdd
    (map_div (PrincipalLaws.BundleCycles.schemePrincipalPointDivisorHom W) (Units.mk0 g hg) (Units.mk0 h hh))
  exact he

theorem schemePrincipalPointDivisor_zpow_div (g h : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField)
    (hg : g ≠ 0) (hh : h ≠ 0) (m n : ℤ) :
    Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W (g ^ n / h ^ m) =
      n • Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W g - m • Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W h := by
  rw [schemePrincipalPointDivisor_div W _ _ (zpow_ne_zero n hg) (zpow_ne_zero m hh)]
  exact congrArg₂ (· - ·)
    (PrincipalLaws.BundleCycles.schemePrincipalPointDivisor_zpow W (Units.mk0 g hg) n)
    (PrincipalLaws.BundleCycles.schemePrincipalPointDivisor_zpow W (Units.mk0 h hh) m)

omit [AlgebraicGeometry.IsNoetherian X] in
theorem supportRegularFunction_ne_zero_of_unit_germ (x : X) (a : Γ(X, ⊤))
    (u : (X.presheaf.stalk x)ˣ)
    (hu : (u : X.presheaf.stalk x) = X.presheaf.germ ⊤ x (by trivial) a) :
    Principal.CartierCycle.BundleCycles.supportRegularFunction a (irreducibleSetEquivPoints.symm x) ≠ 0 := by
  have he := Geometric.ResidueRegular.BundleCycles.pointSupportResidueFunction_regular X x a u hu
  intro hz
  exact Point.SupportResidue.BundleCycles.pointSupportResidueFunction_ne_zero X x
    (Units.map (IsLocalRing.residue (X.presheaf.stalk x)).toMonoidHom u) (he.trans hz)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Support.PrincipalQuotients.BundleCycles
