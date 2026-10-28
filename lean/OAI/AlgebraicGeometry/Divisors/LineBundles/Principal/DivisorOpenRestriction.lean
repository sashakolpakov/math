import OAI.AlgebraicGeometry.Divisors.LineBundles.RationalDivisorRestriction

/-! # Divisor Open Restriction -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.DivisorOpenRestriction.BundleCycles

noncomputable section

/-! # LineBundleCycles: restriction of the whole rational principal-divisor cycle to an open subscheme -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem rationalPrincipalPointDivisor_openRestriction {U X : Scheme.{0}}
    [IsIntegral U] [IsIntegral X] [AlgebraicGeometry.IsNoetherian U]
    [AlgebraicGeometry.IsNoetherian X] (i : U ⟶ X) [IsOpenImmersion i]
    (g : X.functionField) :
    Finsupp.comapDomain i (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X g) i.isOpenEmbedding.injective.injOn =
      RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor U (RationalDivisorRestriction.BundleCycles.openFunctionFieldMap i g) := by
  ext x
  exact congrArg (fun n : ℤ => (n : ℚ)) (RationalDivisorRestriction.BundleCycles.ord_openImmersion i g x).symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.DivisorOpenRestriction.BundleCycles
