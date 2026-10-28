import OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.DivisorLaws
import OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.GlobalSpecialization

/-! # Principal Laws -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Support.PrincipalLaws.BundleCycles

noncomputable section

section

/-!
# LineBundleCycles: group laws for principal divisors on actual supports

Casting the actual integral coefficients to rational numbers and pushing
along the closed support preserve the principal-divisor group laws.
These are the laws needed to combine geometric residue relations.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace _root_.Order

variable {X : Scheme} [AlgebraicGeometry.IsNoetherian X] (W : IrreducibleCloseds X)

theorem schemePrincipalPointDivisor_one : Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W 1 = 0 := by
  unfold Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor
  rw [Principal.DivisorLaws.BundleCycles.principalDivisor_one, Finsupp.mapRange_zero, Finsupp.embDomain_zero]

theorem schemePrincipalPointDivisor_mul (g h : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField)
    (hg : g ≠ 0) (hh : h ≠ 0) :
    Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W (g * h) = Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W g + Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W h := by
  unfold Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor
  rw [Ord.BundleCycles.principalDivisor_mul _ g h hg hh, Finsupp.mapRange_add Int.cast_add, Finsupp.embDomain_add]

def schemePrincipalPointDivisorHom : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionFieldˣ →* Multiplicative (X →₀ ℚ) where
  toFun g := Multiplicative.ofAdd (Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField))
  map_one' := congrArg Multiplicative.ofAdd (schemePrincipalPointDivisor_one W)
  map_mul' g h := congrArg Multiplicative.ofAdd
    (schemePrincipalPointDivisor_mul W (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField)
      (h : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) g.ne_zero h.ne_zero)

theorem schemePrincipalPointDivisor_zpow (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionFieldˣ) (n : ℤ) :
    Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W ((g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) ^ n) =
      n • Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) := by
  have h := congrArg Multiplicative.toAdd (map_zpow (schemePrincipalPointDivisorHom W) g n)
  simp only [schemePrincipalPointDivisorHom, MonoidHom.coe_mk, OneHom.coe_mk,
    Units.val_zpow_eq_zpow_val] at h
  exact h

end

/-! # LineBundleCycles: actual principal-divisor cycles of powers -/

open _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {X : Scheme} [AlgebraicGeometry.IsNoetherian X] (W : IrreducibleCloseds X)

theorem schemePrincipalPointDivisor_pow (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField)
    (hg : g ≠ 0) (n : ℕ) :
    Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W (g ^ n) = (n : ℚ) • Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W g := by
  induction n with
  | zero => simp only [pow_zero, schemePrincipalPointDivisor_one, Nat.cast_zero, zero_smul]
  | succ n ih =>
    rw [pow_succ, schemePrincipalPointDivisor_mul W _ g (pow_ne_zero n hg) hg, ih,
      Nat.cast_add, Nat.cast_one, add_smul, one_smul]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Support.PrincipalLaws.BundleCycles
