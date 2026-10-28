import OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.PrincipalDivisor
import OAI.AlgebraicGeometry.Divisors.LineBundles.Proper.DivisorNorm
import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.DivisorNorm

/-! # Principal Pullback Projection -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Proper.PrincipalPullbackProjection.BundleCycles

noncomputable section

/-! The proper projection formula for the divisor of an actual pulled
rational function, with the native generic residue degree. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    [X.IsSeparated] [Y.IsSeparated] (f : X ⟶ Y) [IsProper f]
    (hη : f (genericPoint X) = genericPoint Y)
    (gY : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType gY]

include gY in
theorem properPushforward_pulledPrincipalDivisor (g : Y.functionFieldˣ) :
    IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward f (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη g.val)) =
      (f.residueDegree (genericPoint X) : ℚ) • RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor Y g.val := by
  let := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.toAlgebra
  have hg : Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη g.val ≠ 0 :=
    (map_ne_zero_iff (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom
      (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.injective).mpr g.ne_zero
  by_cases he : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension gY = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (f ≫ gY)
  · have hfinite := Cycles.Functoriality.FunctionFields.Construction.genericField_extension_finite f hη gY he
    have hn := DivisorNorm.BundleCycles.ProperDivisorNorm.principalDivisor_norm f hη gY hfinite
      (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη g.val) hg
    have hp : Algebra.norm Y.functionField (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη g.val) =
        g.val ^ f.residueDegree (genericPoint X) := by
      change Algebra.norm Y.functionField (algebraMap Y.functionField X.functionField g.val) = _
      rw [Algebra.norm_algebraMap, IntersectionTheory.ProjectionFormula.Support.Fields.genericFieldMap_finrank_eq_residueDegree f hη]
    exact hn.trans ((congrArg (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor Y) hp).trans
      (LineBundles.Finite.DivisorNorm.BundleCycles.rationalPrincipalPointDivisor_pow Y g.val g.ne_zero _))
  · have hd : f.residueDegree (genericPoint X) = 0 := by
      by_contra hd
      have hfinite : Module.Finite Y.functionField X.functionField := by
        apply Module.finite_of_finrank_pos
        rw [IntersectionTheory.ProjectionFormula.Support.Fields.genericFieldMap_finrank_eq_residueDegree f hη]
        exact Nat.pos_of_ne_zero hd
      exact he (LineBundles.Finite.GenericDimension.BundleCycles.schemeDimension_eq_of_finiteGenericMap f hη hfinite gY)
    rw [hd, Nat.cast_zero, zero_smul]
    have hle := Cycles.Functoriality.FunctionFields.Construction.dimension_le_of_genericPoint f hη gY
    by_cases hc : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension gY + 1 = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (f ≫ gY)
    · exact Relative.PrincipalDivisor.BundleCycles.RelativePrincipalDivisor.pushforward_eq_zero f hη gY hc _ hg
    · exact Principal.PushforwardDimensionDrop.BundleCycles.principalDivisor_pushforward_dimension_drop f gY (by omega) _

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Proper.PrincipalPullbackProjection.BundleCycles
