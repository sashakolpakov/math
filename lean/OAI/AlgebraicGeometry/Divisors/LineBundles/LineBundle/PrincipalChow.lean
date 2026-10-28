import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.NormalPrincipalChow
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.FinitePointProjection
import OAI.AlgebraicGeometry.Divisors.LineBundles.NormalizationDivisorPushforward
import OAI.AlgebraicGeometry.Divisors.LineBundles.NormalizationResidue

/-! # Principal Chow -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.PrincipalChow.Cycles

noncomputable section

/-! # LineBundleCycles: line-bundle intersection kills actual principal divisors on singular integral schemes affine over projective schemes -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Scheme OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Fields OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

variable {X Y : Scheme.{0}} [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
    {fY : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation Y fY) (q : X ⟶ Y) [IsAffineHom q]
    (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X) (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (d : ℕ) (hX : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f = d + 2)

include P q hX in
theorem lineBundlePointIntersection_principal_zero (g : X.functionFieldˣ) :
    Point.CycleChow.BundleCycles.pointCycleToChowQ f d (Intersection.Cycles.lineBundlePointIntersection L (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X g.val)) = 0 := by
  let N := IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization X
  let ν := IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap X
  let : IsFinite ν := IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap_isFinite X f
  let : AlgebraicGeometry.IsNoetherian N := NormalizationResidue.BundleCycles.finiteNormalization_noetherian X f
  let gN := NormalizationResidue.BundleCycles.normalizationFunctionUnit X g
  have hN : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (ν ≫ f) = d + 2 := (NormalizationResidue.BundleCycles.finiteNormalization_dimension X f).trans hX
  have hn := NormalPrincipalChow.Cycles.normalLineBundlePointIntersection_principal_zero P (ν ≫ q) (L.pullback ν)
    (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization_stalk_integrallyClosed X) (ν ≫ f) d hN gN
  have hdim : ∀ x : N, RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor N gN.val x ≠ 0 →
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) (ν ≫ f) = d + 1 := by
    intro x hx
    have horder : Ord.BundleCycles.principalDivisor N gN.val x ≠ 0 := by
      intro hz
      apply hx
      change (Ord.BundleCycles.principalDivisor N gN.val x : ℚ) = 0
      rw [hz, Int.cast_zero]
    have hc := Normal.PointResidue.BundleCycles.principalDivisor_support_coheight N gN.val x (Finsupp.mem_support_iff.mpr horder)
    have hd := DivisorClass.Chern.SupportCodimension.Construction.pointClosure_dimension_add_one (ν ≫ f) x hc
    omega
  have hp := FinitePointProjection.Cycles.lineBundlePointIntersection_finite_projection ν f L d (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor N gN.val) hdim
  have hz := congrArg (Finite.ChowPushforward.BundleCycles.finiteChowPushforward ν f d) hn
  rw [map_zero] at hz
  have he := hp.symm.trans hz
  have hg := NormalizationDivisorPushforward.BundleCycles.normalizationPrincipalDivisor_pushforward X f g.val g.ne_zero
  exact (congrArg (fun z => Point.CycleChow.BundleCycles.pointCycleToChowQ f d (Intersection.Cycles.lineBundlePointIntersection L z)) hg).symm.trans he

include P q hX in
theorem lineBundlePointIntersection_principal_nonzero (g : X.functionField) (hg : g ≠ 0) :
    Point.CycleChow.BundleCycles.pointCycleToChowQ f d (Intersection.Cycles.lineBundlePointIntersection L (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X g)) = 0 :=
  lineBundlePointIntersection_principal_zero P q L f d hX (Units.mk0 g hg)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.PrincipalChow.Cycles
