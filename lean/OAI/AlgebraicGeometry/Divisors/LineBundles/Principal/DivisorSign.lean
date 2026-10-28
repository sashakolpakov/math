import OAI.AlgebraicGeometry.Divisors.LineBundles.Support.PrincipalLaws

/-! # Divisor Sign -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.DivisorSign.BundleCycles

noncomputable section

/-!
# LineBundleCycles: signs have zero actual principal divisor

The divisor homomorphism takes a function whose square is one to an
integral cycle killed by two. Every coefficient is therefore zero.
This applies to all integer powers of the constant sign -1.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

universe u
variable (X : Scheme.{u}) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]

theorem principalDivisor_of_square_one (g : X.functionField) (hg : g * g = 1) :
    Ord.BundleCycles.principalDivisor X g = 0 := by
  have hgne : g ≠ 0 := by intro hz; simp [hz] at hg
  have hd := Ord.BundleCycles.principalDivisor_mul X g g hgne hgne
  rw [hg, DivisorLaws.BundleCycles.principalDivisor_one] at hd
  ext x
  have hc := congrArg (fun c : X →₀ ℤ => c x) hd
  change (0 : ℤ) = Ord.BundleCycles.principalDivisor X g x + Ord.BundleCycles.principalDivisor X g x at hc
  change Ord.BundleCycles.principalDivisor X g x = 0
  omega

variable {Y : Scheme} [AlgebraicGeometry.IsNoetherian Y]

theorem schemePrincipalPointDivisor_sign (W : IrreducibleCloseds Y) (n : ℤ) :
    Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W ((-1 : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) ^ n) = 0 := by
  have hs : ((-1 : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) ^ n) * ((-1) ^ n) = 1 := by
    rw [← mul_zpow, neg_mul_neg, one_mul, one_zpow]
  unfold Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor
  rw [principalDivisor_of_square_one _ _ hs, Finsupp.mapRange_zero, Finsupp.embDomain_zero]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.DivisorSign.BundleCycles
