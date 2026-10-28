import OAI.AlgebraicGeometry.Divisors.LineBundles.Support.PuncturedFunctionField
import OAI.AlgebraicGeometry.Divisors.LineBundles.Laurent.DivisorPullback
import OAI.AlgebraicGeometry.Divisors.LineBundles.Support.SpecializationLocality

/-! # Punctured Divisor -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Support.PuncturedDivisor.BundleCycles

noncomputable section

/-! # LineBundleCycles: full rational divisors on punctured deformations of arbitrary integral supports -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite

variable {X : Scheme.{0}} (I P : X.IdealSheafData)

def supportPuncturedCycleExtension : (P.subscheme →₀ ℚ) →ₗ[ℚ] (LaurentChart.BundleCycles.supportPuncturedDeformation I P →₀ ℚ) :=
  Finsupp.lmapDomain ℚ ℚ (PuncturedGenericPoint.BundleCycles.supportPuncturedGenericPoint I P)

variable [IsIntegral P.subscheme] [AlgebraicGeometry.IsNoetherian X]

instance supportDivisorBase_noetherian : AlgebraicGeometry.IsNoetherian P.subscheme := by
  have : IsLocallyNoetherian P.subscheme := LocallyOfFiniteType.isLocallyNoetherian P.subschemeι
  have : CompactSpace P.subscheme := QuasiCompact.compactSpace_of_compactSpace P.subschemeι
  exact ⟨⟩

theorem supportPuncturedOrder_on_chart (U : X.AffineZariskiSite)
    [Nonempty (Spec ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U)))]
    (g : P.subscheme.functionField)
    (Q : Spec (CommRingCat.of (LaurentPolynomial ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U))))) :
    (LaurentChart.BundleCycles.supportPuncturedDeformation I P).ord (PuncturedFunctionField.BundleCycles.supportPuncturedFunctionFieldMap I P g)
        (LaurentChart.BundleCycles.supportPuncturedLaurentChart I P U Q) =
      (Spec (CommRingCat.of (LaurentPolynomial ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U))))).ord
        (Laurent.FiberGenericPoint.BundleCycles.laurentFunctionFieldMap ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U))
          (RationalDivisorRestriction.BundleCycles.openFunctionFieldMap (Projection.BundleCycles.supportCoefficientChart P U) g)) Q := by
  have h := congrArg (fun k => k g) (PuncturedFunctionField.BundleCycles.supportPuncturedFunctionFieldMap_on_chart I P U)
  exact (RationalDivisorRestriction.BundleCycles.ord_openImmersion (LaurentChart.BundleCycles.supportPuncturedLaurentChart I P U)
    (PuncturedFunctionField.BundleCycles.supportPuncturedFunctionFieldMap I P g) Q).symm.trans
      (congrArg (fun a => (Spec (CommRingCat.of
        (LaurentPolynomial ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U))))).ord a Q) h)

theorem supportPuncturedProjection_order (x : P.subscheme) (g : P.subscheme.functionField) :
    (LaurentChart.BundleCycles.supportPuncturedDeformation I P).ord (PuncturedFunctionField.BundleCycles.supportPuncturedFunctionFieldMap I P g)
        (PuncturedGenericPoint.BundleCycles.supportPuncturedGenericPoint I P x) = P.subscheme.ord g x := by
  obtain ⟨U, p, hp⟩ := P.subschemeCover.openCover.exists_eq x
  change X.AffineZariskiSite at U
  have : Nonempty (Spec ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U))) := ⟨p⟩
  have : IsDomain ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U)) := Integrality.BundleCycles.supportCoefficientRing_isDomain P U
  have he := PuncturedGenericPoint.BundleCycles.supportPuncturedGenericPoint_on_chart I P U p
  exact (congrArg (fun z => (LaurentChart.BundleCycles.supportPuncturedDeformation I P).ord (PuncturedFunctionField.BundleCycles.supportPuncturedFunctionFieldMap I P g)
    (PuncturedGenericPoint.BundleCycles.supportPuncturedGenericPoint I P z)) hp.symm).trans
      ((congrArg ((LaurentChart.BundleCycles.supportPuncturedDeformation I P).ord (PuncturedFunctionField.BundleCycles.supportPuncturedFunctionFieldMap I P g)) he).trans
        ((supportPuncturedOrder_on_chart I P U g _).trans
          ((@Laurent.DivisorPullback.BundleCycles.laurentProjection_order ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U)) _
            (Integrality.BundleCycles.supportCoefficientRing_isDomain P U) (SpecializationLocality.BundleCycles.supportCoefficientRing_noetherian P U) p
            (RationalDivisorRestriction.BundleCycles.openFunctionFieldMap (Projection.BundleCycles.supportCoefficientChart P U) g)).trans
              ((RationalDivisorRestriction.BundleCycles.ord_openImmersion (Projection.BundleCycles.supportCoefficientChart P U) g p).trans
                (congrArg (P.subscheme.ord g) hp)))))

theorem supportPuncturedPulledDivisor_support (g : P.subscheme.functionField) (hg : g ≠ 0)
    (y : LaurentChart.BundleCycles.supportPuncturedDeformation I P)
    (hy : (LaurentChart.BundleCycles.supportPuncturedDeformation I P).ord (PuncturedFunctionField.BundleCycles.supportPuncturedFunctionFieldMap I P g) y ≠ 0) :
    y ∈ Set.range (PuncturedGenericPoint.BundleCycles.supportPuncturedGenericPoint I P) := by
  obtain ⟨U, Q, rfl⟩ := LaurentChart.BundleCycles.supportPuncturedLaurentChart_covers I P y
  change X.AffineZariskiSite at U
  have : Nonempty (Spec ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U))) :=
    ⟨Laurent.FiberGenericPoint.BundleCycles.laurentProjection ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U)) Q⟩
  have : IsDomain ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U)) := Integrality.BundleCycles.supportCoefficientRing_isDomain P U
  have hg' : RationalDivisorRestriction.BundleCycles.openFunctionFieldMap (Projection.BundleCycles.supportCoefficientChart P U) g ≠ 0 :=
    (map_ne_zero_iff _ (RationalDivisorRestriction.BundleCycles.openFunctionFieldMap (Projection.BundleCycles.supportCoefficientChart P U)).hom.injective).mpr hg
  have hQ : (Spec (CommRingCat.of (LaurentPolynomial ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U))))).ord
      (Laurent.FiberGenericPoint.BundleCycles.laurentFunctionFieldMap ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U))
        (RationalDivisorRestriction.BundleCycles.openFunctionFieldMap (Projection.BundleCycles.supportCoefficientChart P U) g)) Q ≠ 0 :=
    fun hz => hy ((supportPuncturedOrder_on_chart I P U g Q).trans hz)
  obtain ⟨p, rfl⟩ := @Laurent.DivisorPullback.BundleCycles.laurentPulledDivisor_support ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U)) _
    (Integrality.BundleCycles.supportCoefficientRing_isDomain P U) (SpecializationLocality.BundleCycles.supportCoefficientRing_noetherian P U) _ hg' Q hQ
  exact ⟨Projection.BundleCycles.supportCoefficientChart P U p, PuncturedGenericPoint.BundleCycles.supportPuncturedGenericPoint_on_chart I P U p⟩

theorem supportPuncturedPrincipalDivisor_pullback (g : P.subscheme.functionField) (hg : g ≠ 0) :
    RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (LaurentChart.BundleCycles.supportPuncturedDeformation I P) (PuncturedFunctionField.BundleCycles.supportPuncturedFunctionFieldMap I P g) =
      supportPuncturedCycleExtension I P (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor P.subscheme g) := by
  ext y
  by_cases hy : y ∈ Set.range (PuncturedGenericPoint.BundleCycles.supportPuncturedGenericPoint I P)
  · obtain ⟨x, rfl⟩ := hy
    change _ = Finsupp.mapDomain (PuncturedGenericPoint.BundleCycles.supportPuncturedGenericPoint I P) _ (PuncturedGenericPoint.BundleCycles.supportPuncturedGenericPoint I P x)
    rw [Finsupp.mapDomain_apply_of_injective (PuncturedGenericPoint.BundleCycles.supportPuncturedGenericPoint_injective I P),
      RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor_apply, RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor_apply, supportPuncturedProjection_order]
  · have hz : (LaurentChart.BundleCycles.supportPuncturedDeformation I P).ord (PuncturedFunctionField.BundleCycles.supportPuncturedFunctionFieldMap I P g) y = 0 := by
      by_contra hn
      exact hy (supportPuncturedPulledDivisor_support I P g hg y hn)
    change _ = Finsupp.mapDomain (PuncturedGenericPoint.BundleCycles.supportPuncturedGenericPoint I P) _ y
    rw [Finsupp.mapDomain_of_notMem_range _ _ hy, RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor_apply, hz, Int.cast_zero]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Support.PuncturedDivisor.BundleCycles
