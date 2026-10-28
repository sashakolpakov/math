import OAI.AlgebraicGeometry.Divisors.LineBundles.DVRResidueOf
import OAI.AlgebraicGeometry.Divisors.LineBundles.Geometric.ResidueRegular
import OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.CartierCycle

/-! # Factored Residue -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Geometric.FactoredResidue.BundleCycles

noncomputable section

/-!
# LineBundleCycles: factored residues are actual restricted rational functions

The residue-field isomorphism preserves quotients and powers. Local
units represented by ambient sections therefore give their actual
restrictions on the reduced prime support.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable (X : Scheme) (x : X)

theorem pointSupportResidueFunction_div (r s : (X.residueField x)ˣ) :
    Point.SupportResidue.BundleCycles.pointSupportResidueFunction X x (r / s) =
      Point.SupportResidue.BundleCycles.pointSupportResidueFunction X x r / Point.SupportResidue.BundleCycles.pointSupportResidueFunction X x s := by
  unfold Point.SupportResidue.BundleCycles.pointSupportResidueFunction
  rw [Units.val_div_eq_div_val]
  exact map_div₀ (Point.SupportResidue.BundleCycles.pointSupportResidueIso X x).hom.hom _ _

theorem pointSupportResidueFunction_zpow (r : (X.residueField x)ˣ) (m : ℤ) :
    Point.SupportResidue.BundleCycles.pointSupportResidueFunction X x (r ^ m) = (Point.SupportResidue.BundleCycles.pointSupportResidueFunction X x r) ^ m := by
  unfold Point.SupportResidue.BundleCycles.pointSupportResidueFunction
  rw [Units.val_zpow_eq_zpow_val]
  exact map_zpow₀ (Point.SupportResidue.BundleCycles.pointSupportResidueIso X x).hom.hom _ _

theorem pointSupportResidueFunction_quotient_regular (a c : Γ(X, ⊤))
    (u s : (X.presheaf.stalk x)ˣ)
    (hu : (u : X.presheaf.stalk x) = X.presheaf.germ ⊤ x (by trivial) a)
    (hs : (s : X.presheaf.stalk x) = X.presheaf.germ ⊤ x (by trivial) c) :
    Point.SupportResidue.BundleCycles.pointSupportResidueFunction X x (Units.map (IsLocalRing.residue (X.presheaf.stalk x)).toMonoidHom (u / s)) =
      Principal.CartierCycle.BundleCycles.supportRegularFunction a (irreducibleSetEquivPoints.symm x) /
        Principal.CartierCycle.BundleCycles.supportRegularFunction c (irreducibleSetEquivPoints.symm x) := by
  let ru : (X.residueField x)ˣ := Units.map (IsLocalRing.residue (X.presheaf.stalk x)).toMonoidHom u
  let rs : (X.residueField x)ˣ := Units.map (IsLocalRing.residue (X.presheaf.stalk x)).toMonoidHom s
  have he : Units.map (IsLocalRing.residue (X.presheaf.stalk x)).toMonoidHom (u / s) = ru / rs :=
    map_div _ u s
  exact (congrArg (Point.SupportResidue.BundleCycles.pointSupportResidueFunction X x) he).trans
    ((pointSupportResidueFunction_div X x ru rs).trans
      (congrArg₂ (· / ·) (ResidueRegular.BundleCycles.pointSupportResidueFunction_regular X x a u hu)
        (ResidueRegular.BundleCycles.pointSupportResidueFunction_regular X x c s hs)))

variable [IsIntegral X] [IsDiscreteValuationRing (X.presheaf.stalk x)]

theorem geometricResidueFunction_of_factors (π : X.presheaf.stalk x) (hπ : Irreducible π)
    (g h : X.functionFieldˣ) (u v : (X.presheaf.stalk x)ˣ) (m n : ℤ)
    (hg : (g : X.functionField) = u • (algebraMap (X.presheaf.stalk x) X.functionField π) ^ m)
    (hh : (h : X.functionField) = v • (algebraMap (X.presheaf.stalk x) X.functionField π) ^ n) :
    ResidueFunction.BundleCycles.geometricResidueFunction X x π hπ g h =
      (Point.SupportResidue.BundleCycles.pointSupportResidueFunction X x (Units.map (IsLocalRing.residue (X.presheaf.stalk x)).toMonoidHom u)) ^ n /
        (Point.SupportResidue.BundleCycles.pointSupportResidueFunction X x (Units.map (IsLocalRing.residue (X.presheaf.stalk x)).toMonoidHom v)) ^ m := by
  let ru : (X.residueField x)ˣ := Units.map (IsLocalRing.residue (X.presheaf.stalk x)).toMonoidHom u
  let rv : (X.residueField x)ˣ := Units.map (IsLocalRing.residue (X.presheaf.stalk x)).toMonoidHom v
  have he : DVRResidueOf.BundleCycles.dvrResidueQuotient π hπ g h = ru ^ n / rv ^ m :=
    DVRResidueOf.BundleCycles.dvrResidueQuotient_of_factors π hπ g h u v m n hg hh
  exact (congrArg (Point.SupportResidue.BundleCycles.pointSupportResidueFunction X x) he).trans
    ((pointSupportResidueFunction_div X x (ru ^ n) (rv ^ m)).trans
      (congrArg₂ (· / ·) (pointSupportResidueFunction_zpow X x ru n)
        (pointSupportResidueFunction_zpow X x rv m)))

theorem geometricResidueFunction_of_quotient_factors (π : X.presheaf.stalk x) (hπ : Irreducible π)
    (g h : X.functionFieldˣ) (a c b d : Γ(X, ⊤)) (u s v w : (X.presheaf.stalk x)ˣ) (m n : ℤ)
    (hu : (u : X.presheaf.stalk x) = X.presheaf.germ ⊤ x (by trivial) a)
    (hs : (s : X.presheaf.stalk x) = X.presheaf.germ ⊤ x (by trivial) c)
    (hv : (v : X.presheaf.stalk x) = X.presheaf.germ ⊤ x (by trivial) b)
    (hw : (w : X.presheaf.stalk x) = X.presheaf.germ ⊤ x (by trivial) d)
    (hg : (g : X.functionField) = (u / s) • (algebraMap (X.presheaf.stalk x) X.functionField π) ^ m)
    (hh : (h : X.functionField) = (v / w) • (algebraMap (X.presheaf.stalk x) X.functionField π) ^ n) :
    ResidueFunction.BundleCycles.geometricResidueFunction X x π hπ g h =
      (Principal.CartierCycle.BundleCycles.supportRegularFunction a (irreducibleSetEquivPoints.symm x) /
        Principal.CartierCycle.BundleCycles.supportRegularFunction c (irreducibleSetEquivPoints.symm x)) ^ n /
      (Principal.CartierCycle.BundleCycles.supportRegularFunction b (irreducibleSetEquivPoints.symm x) /
        Principal.CartierCycle.BundleCycles.supportRegularFunction d (irreducibleSetEquivPoints.symm x)) ^ m := by
  rw [geometricResidueFunction_of_factors X x π hπ g h (u / s) (v / w) m n hg hh,
    pointSupportResidueFunction_quotient_regular X x a c u s hu hs,
    pointSupportResidueFunction_quotient_regular X x b d v w hv hw]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Geometric.FactoredResidue.BundleCycles
