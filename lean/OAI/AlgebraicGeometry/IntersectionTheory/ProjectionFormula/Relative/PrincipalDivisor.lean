import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.CurveZeros
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.Divisor
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.Inversion
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.DivisorComparison

/-! # Principal Divisor -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.PrincipalDivisor

noncomputable section

/-! Proper pushforward kills principal divisors when the source and
its image differ by one dimension. The proof includes singular sources
via their actual finite normalization. -/

set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.DivisorNorm OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PositiveCycle
  Normalization.Scheme Normalization.Fields Generic.FiberFields

theorem pushforward_eq_zero_of_normal {K : Type} [Field K] [CharZero K]
    {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] [X.IsSeparated] [Y.IsSeparated]
    [AlgebraicGeometry.IsNoetherian X]
    (f : X ⟶ Y) [IsProper f] (hη : f (genericPoint X) = genericPoint Y)
    (gY : Y ⟶ Spec (.of K)) [LocallyOfFiniteType gY] [LocallyOfFiniteType (f ≫ gY)]
    (hdim : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension gY + 1 = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (f ≫ gY))
    (hNormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (g : X.functionField) (hg : g ≠ 0) : CyclePushforward.pointPushforward f (Affine.DivisorNorm.rationalPrincipalDivisor X g) = 0 := by
  let := Generic.FiberFields.fieldAlgebra f hη
  by_cases ha : IsAlgebraic Y.functionField g
  · exact Divisor.principalDivisor_pushforward f hη gY hdim hNormal g hg ha
  · have hai : Transcendental Y.functionField g⁻¹ := by
      intro h
      exact ha (by simpa only [inv_inv] using h.inv)
    have hz := CurveZeros.positiveDivisor_pushforward f hη gY hdim hNormal g ha
    have hp := CurveZeros.positiveDivisor_pushforward f hη gY hdim hNormal g⁻¹ hai
    have hd := Parameter.Inversion.parameter_finrank_inv Y.functionField X.functionField g ha hai
    have he : CyclePushforward.pointPushforward f (PositiveCycle.positivePart (Affine.DivisorNorm.rationalPrincipalDivisor X g)) =
        CyclePushforward.pointPushforward f (PositiveCycle.positivePart (Affine.DivisorNorm.rationalPrincipalDivisor X g⁻¹)) := by
      rw [hz, hp]
      exact congrArg (fun n : ℕ => Finsupp.single (genericPoint Y) (n : ℚ)) hd
    rw [PositiveCycle.principalDivisor_eq_positive_sub_inverse g, map_sub, he, sub_self]

theorem pushforward_eq_zero {K : Type} [Field K] [CharZero K]
    {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] [X.IsSeparated] [Y.IsSeparated]
    [AlgebraicGeometry.IsNoetherian X]
    (f : X ⟶ Y) [IsProper f] (hη : f (genericPoint X) = genericPoint Y)
    (gY : Y ⟶ Spec (.of K)) [LocallyOfFiniteType gY] [LocallyOfFiniteType (f ≫ gY)]
    (hdim : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension gY + 1 = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (f ≫ gY))
    (g : X.functionField) (hg : g ≠ 0) : CyclePushforward.pointPushforward f (Affine.DivisorNorm.rationalPrincipalDivisor X g) = 0 := by
  let := Normalization.DivisorComparison.normalization_noetherian X (f ≫ gY)
  let : IsFinite (Normalization.Scheme.normalizationMap X) := Normalization.Scheme.normalizationMap_isFinite X (f ≫ gY)
  let : (Normalization.Scheme.normalization X).IsSeparated := ⟨by
    rw [← Limits.terminal.comp_from (Normalization.Scheme.normalizationMap X)]
    infer_instance⟩
  let : IsIso (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (Normalization.Scheme.normalizationMap X) (Normalization.Fields.normalizationMap_genericPoint X)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (Normalization.Fields.normalizationFieldMap_bijective X)
  have hd : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension gY + 1 =
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension ((Normalization.Scheme.normalizationMap X ≫ f) ≫ gY) := by
    rw [Category.assoc]
    exact hdim.trans (BirationalPrincipalDivisor.dimension_eq_of_birational
      (Normalization.Scheme.normalizationMap X) (Normalization.Fields.normalizationMap_genericPoint X) (f ≫ gY))
  have hη' : (Normalization.Scheme.normalizationMap X ≫ f) (genericPoint (Normalization.Scheme.normalization X)) = genericPoint Y :=
    (congrArg f (Normalization.Fields.normalizationMap_genericPoint X)).trans hη
  have hg' : (Normalization.Fields.normalizationFieldIso X).hom g ≠ 0 :=
    (map_ne_zero_iff _ (Normalization.Fields.normalizationFieldMap_bijective X).injective).mpr hg
  have hn := pushforward_eq_zero_of_normal (Normalization.Scheme.normalizationMap X ≫ f) hη' gY hd
    (Normalization.Scheme.normalization_stalk_integrallyClosed X) ((Normalization.Fields.normalizationFieldIso X).hom g) hg'
  have hc := DFunLike.congr_fun (CyclePushforward.pointPushforward_comp (Normalization.Scheme.normalizationMap X) f)
    (Affine.DivisorNorm.rationalPrincipalDivisor (Normalization.Scheme.normalization X) ((Normalization.Fields.normalizationFieldIso X).hom g))
  change CyclePushforward.pointPushforward (Normalization.Scheme.normalizationMap X ≫ f) _ = CyclePushforward.pointPushforward f
    (CyclePushforward.pointPushforward (Normalization.Scheme.normalizationMap X) _) at hc
  rw [Normalization.DivisorComparison.normalization_principalDivisor X (f ≫ gY) g hg] at hc
  exact hc.symm.trans hn

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.PrincipalDivisor
