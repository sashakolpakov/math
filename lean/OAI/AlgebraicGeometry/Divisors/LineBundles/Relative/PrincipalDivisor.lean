import OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.CurveZeros
import OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.Divisor
import OAI.AlgebraicGeometry.Divisors.LineBundles.ParameterInversionInv
import OAI.AlgebraicGeometry.Divisors.LineBundles.NormalizationDivisorPushforward

/-! # Principal Divisor -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.PrincipalDivisor.BundleCycles.RelativePrincipalDivisor

noncomputable section

/-! Proper pushforward kills principal divisors when the source and
its image differ by one dimension. The proof includes singular sources
via their actual finite normalization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Divisors.LineBundles.NormalizationDivisorPushforward.BundleCycles OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward OAI.AlgebraicGeometry.Divisors.LineBundles.PositiveCycleEq.BundleCycles.PositiveCycle
  IntersectionTheory.ProjectionFormula.Normalization.Scheme IntersectionTheory.ProjectionFormula.Normalization.Fields GenericFiberEss.BundleCycles.GenericFiberFields

theorem pushforward_eq_zero_of_normal {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] [X.IsSeparated] [Y.IsSeparated]
    [AlgebraicGeometry.IsNoetherian X]
    (f : X ⟶ Y) [IsProper f] (hη : f (genericPoint X) = genericPoint Y)
    (gY : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType gY] [LocallyOfFiniteType (f ≫ gY)]
    (hdim : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension gY + 1 = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (f ≫ gY))
    (hNormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (g : X.functionField) (hg : g ≠ 0) : IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward f (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X g) = 0 := by
  let := GenericFiberEss.BundleCycles.GenericFiberFields.fieldAlgebra f hη
  by_cases ha : IsAlgebraic Y.functionField g
  · exact Divisor.BundleCycles.RelativeAlgebraicDivisor.principalDivisor_pushforward f hη gY hdim hNormal g hg ha
  · have hai : Transcendental Y.functionField g⁻¹ := by
      intro h
      exact ha (by simpa only [inv_inv] using h.inv)
    have hz := CurveZeros.BundleCycles.RelativeCurveZeros.positiveDivisor_pushforward f hη gY hdim hNormal g ha
    have hp := CurveZeros.BundleCycles.RelativeCurveZeros.positiveDivisor_pushforward f hη gY hdim hNormal g⁻¹ hai
    have hd := ParameterInversionInv.BundleCycles.ParameterInversion.parameter_finrank_inv Y.functionField X.functionField g ha hai
    have he : IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward f (PositiveCycleEq.BundleCycles.PositiveCycle.positivePart (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X g)) =
        IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward f (PositiveCycleEq.BundleCycles.PositiveCycle.positivePart (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X g⁻¹)) := by
      rw [hz, hp]
      exact congrArg (fun n : ℕ => Finsupp.single (genericPoint Y) (n : ℚ)) hd
    rw [PositiveCycleEq.BundleCycles.PositiveCycle.principalDivisor_eq_positive_sub_inverse g, map_sub, he, sub_self]

theorem pushforward_eq_zero {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] [X.IsSeparated] [Y.IsSeparated]
    [AlgebraicGeometry.IsNoetherian X]
    (f : X ⟶ Y) [IsProper f] (hη : f (genericPoint X) = genericPoint Y)
    (gY : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType gY] [LocallyOfFiniteType (f ≫ gY)]
    (hdim : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension gY + 1 = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (f ≫ gY))
    (g : X.functionField) (hg : g ≠ 0) : IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward f (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X g) = 0 := by
  let := NormalizationResidue.BundleCycles.finiteNormalization_noetherian X (f ≫ gY)
  let : IsFinite (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap X) := IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap_isFinite X (f ≫ gY)
  let : (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization X).IsSeparated := ⟨by
    rw [← Limits.terminal.comp_from (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap X)]
    infer_instance⟩
  let : IsIso (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap X) (IntersectionTheory.ProjectionFormula.Normalization.Fields.normalizationMap_genericPoint X)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (IntersectionTheory.ProjectionFormula.Normalization.Fields.normalizationFieldMap_bijective X)
  have hd : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension gY + 1 =
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension ((IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap X ≫ f) ≫ gY) := by
    rw [Category.assoc]
    exact hdim.trans (Proper.BirationalPrincipalDivisor.BundleCycles.schemeDimension_eq_of_birational
      (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap X) (IntersectionTheory.ProjectionFormula.Normalization.Fields.normalizationMap_genericPoint X) (f ≫ gY))
  have hη' : (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap X ≫ f) (genericPoint (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization X)) = genericPoint Y :=
    (congrArg f (IntersectionTheory.ProjectionFormula.Normalization.Fields.normalizationMap_genericPoint X)).trans hη
  have hg' : (IntersectionTheory.ProjectionFormula.Normalization.Fields.normalizationFieldIso X).hom g ≠ 0 :=
    (map_ne_zero_iff _ (IntersectionTheory.ProjectionFormula.Normalization.Fields.normalizationFieldMap_bijective X).injective).mpr hg
  have hn := pushforward_eq_zero_of_normal (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap X ≫ f) hη' gY hd
    (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization_stalk_integrallyClosed X) ((IntersectionTheory.ProjectionFormula.Normalization.Fields.normalizationFieldIso X).hom g) hg'
  have hc := DFunLike.congr_fun (IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward_comp (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap X) f)
    (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization X) ((IntersectionTheory.ProjectionFormula.Normalization.Fields.normalizationFieldIso X).hom g))
  change IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap X ≫ f) _ = IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward f
    (IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap X) _) at hc
  rw [NormalizationDivisorPushforward.BundleCycles.normalizationPrincipalDivisor_pushforward X (f ≫ gY) g hg] at hc
  exact hc.symm.trans hn

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.PrincipalDivisor.BundleCycles.RelativePrincipalDivisor
