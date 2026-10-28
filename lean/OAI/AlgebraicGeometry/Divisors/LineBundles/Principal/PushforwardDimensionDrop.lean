import OAI.AlgebraicGeometry.Divisors.LineBundles.Proper.BirationalPrincipalDivisor
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.ChowIntersection
import OAI.AlgebraicGeometry.Divisors.LineBundles.Point.DimensionBound

/-! # Pushforward Dimension Drop -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.PushforwardDimensionDrop.BundleCycles

noncomputable section

/-! # LineBundleCycles: losing at least two dimensions kills the actual residue-weighted pushforward of every principal divisor -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace _root_.Order

theorem pointDimension_le_schemeDimension {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (x : X) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) f ≤ Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f := by
  have h := Point.DimensionBound.BundleCycles.coheight_add_pointDimension_le f x
  have h' : (Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) f : ℕ∞) ≤
      (Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f : ℕ∞) := le_trans (le_add_left le_rfl) h
  exact_mod_cast h'

theorem principalDivisor_pushforward_dimension_drop {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    [AlgebraicGeometry.IsNoetherian X] (f : X ⟶ Y) (gY : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)
    [LocallyOfFiniteType gY] [LocallyOfFiniteType (f ≫ gY)]
    (hdim : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension gY + 1 < Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (f ≫ gY))
    (g : X.functionField) : IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward f (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X g) = 0 := by
  ext y
  apply Proper.BirationalPrincipalDivisor.BundleCycles.pointPushforward_eq_zero_of_degrees
  intro x hx _
  by_contra hd
  have hs := LineBundle.ChowIntersection.Cycles.rationalPrincipalPointDivisor_dimension X (f ≫ gY) g x hx
  have he := Finite.GenericDimension.BundleCycles.pointClosure_dimension_of_nonzeroResidueDegree f gY x hd
  have hl := pointDimension_le_schemeDimension gY (f x)
  omega

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.PushforwardDimensionDrop.BundleCycles
