import OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.InfinityGluing
import OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.SupportCover

/-! # Infinity Support -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.InfinitySupport.BundleCycles

noncomputable section

/-! The actual infinity hyperplane has a compatible projection to the closed center. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite

variable {X : Scheme.{0}} (I : X.IdealSheafData)

def conormalInfinityChartToSupport (U : X.AffineZariskiSite) : InfinityDiagram.BundleCycles.conormalInfinityChart I U ⟶ I.subscheme :=
  (InfinityGluing.BundleCycles.conormalInfinityToCoefficients I).app U ≫ Support.Projection.BundleCycles.supportCoefficientChart I U

theorem conormalInfinityChartToSupport_toBase (U : X.AffineZariskiSite) :
    conormalInfinityChartToSupport I U ≫ I.subschemeι =
      (InfinityGluing.BundleCycles.conormalInfinityGlueData I).natTrans.app U ≫ U.1.ι := by
  let q := CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U))
  have hq : Support.Projection.BundleCycles.supportCoefficientChart I U ≫ I.subschemeι =
      (Spec.map q ≫ U.2.isoSpec.inv) ≫ U.1.ι := I.subschemeCover_map_subschemeι U
  change ((InfinityGluing.BundleCycles.conormalInfinityToCoefficients I).app U ≫ Support.Projection.BundleCycles.supportCoefficientChart I U) ≫ I.subschemeι =
    ((InfinityGluing.BundleCycles.conormalInfinityToCoefficients I).app U ≫ (Spec.map q ≫ U.2.isoSpec.inv)) ≫ U.1.ι
  rw [Category.assoc, hq]
  simp only [Category.assoc]
  rfl

def conormalInfinitySupportCocone : Cocone (InfinityGluing.BundleCycles.conormalInfinityGlueData I).functor where
  pt := I.subscheme
  ι.app U := conormalInfinityChartToSupport I U
  ι.naturality {U V} f := by
    apply (cancel_mono I.subschemeι).mp
    have h : (InfinityGluing.BundleCycles.conormalInfinityGlueData I).functor.map f ≫
        ((InfinityGluing.BundleCycles.conormalInfinityGlueData I).natTrans.app V ≫ V.1.ι) =
      (InfinityGluing.BundleCycles.conormalInfinityGlueData I).natTrans.app U ≫ U.1.ι :=
      (((InfinityGluing.BundleCycles.conormalInfinityGlueData I).natTrans ≫
        (directedCover X).functorOfLocallyDirectedHomBase).naturality f).trans (Category.comp_id _)
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => (InfinityGluing.BundleCycles.conormalInfinityGlueData I).functor.map f ≫ k)
        (conormalInfinityChartToSupport_toBase I V)).trans
      (h.trans ((conormalInfinityChartToSupport_toBase I U).symm.trans
        (congrArg (fun k => k ≫ I.subschemeι)
          (Category.comp_id (conormalInfinityChartToSupport I U)).symm))))

def globalConormalInfinityToSupport : InfinityGluing.BundleCycles.globalConormalInfinity I ⟶ I.subscheme :=
  colimit.desc _ (conormalInfinitySupportCocone I)

theorem globalConormalInfinityToSupport_on_chart (U : X.AffineZariskiSite) :
    (InfinityGluing.BundleCycles.globalConormalInfinityCover I).f U ≫ globalConormalInfinityToSupport I =
      conormalInfinityChartToSupport I U := colimit.ι_desc (conormalInfinitySupportCocone I) U

theorem globalConormalInfinityToSupport_toBase :
    globalConormalInfinityToSupport I ≫ I.subschemeι = InfinityGluing.BundleCycles.globalConormalInfinityToBase I := by
  apply (InfinityGluing.BundleCycles.globalConormalInfinityCover I).hom_ext
  intro U
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ I.subschemeι) (globalConormalInfinityToSupport_on_chart I U)).trans
      ((conormalInfinityChartToSupport_toBase I U).trans
        ((InfinityGluing.BundleCycles.conormalInfinityGlueData I).ι_toBase U).symm))

instance globalConormalInfinityCover_isOpenImmersion (U : X.AffineZariskiSite) :
    IsOpenImmersion ((InfinityGluing.BundleCycles.globalConormalInfinityCover I).f U) := (InfinityGluing.BundleCycles.globalConormalInfinityCover I).map_prop U

theorem globalConormalInfinityToBase_preimage (U : X.AffineZariskiSite) :
    InfinityGluing.BundleCycles.globalConormalInfinityToBase I ⁻¹ᵁ U.1 = ((InfinityGluing.BundleCycles.globalConormalInfinityCover I).f U).opensRange := by
  have h := (InfinityGluing.BundleCycles.conormalInfinityGlueData I).toBase_preimage_eq_opensRange_ι U
  change InfinityGluing.BundleCycles.globalConormalInfinityToBase I ⁻¹ᵁ U.1.ι.opensRange =
    ((InfinityGluing.BundleCycles.globalConormalInfinityCover I).f U).opensRange at h
  rw [Scheme.Opens.opensRange_ι] at h
  exact h

theorem globalConormalInfinityToSupport_preimage (U : X.AffineZariskiSite) :
    globalConormalInfinityToSupport I ⁻¹ᵁ (Support.Projection.BundleCycles.supportCoefficientChart I U).opensRange =
      ((InfinityGluing.BundleCycles.globalConormalInfinityCover I).f U).opensRange := by
  rw [Support.Projection.BundleCycles.supportCoefficientChart_range, ← Scheme.Hom.comp_preimage,
    globalConormalInfinityToSupport_toBase, globalConormalInfinityToBase_preimage]

theorem globalConormalInfinityToSupport_chart_isPullback (U : X.AffineZariskiSite) :
    IsPullback ((InfinityGluing.BundleCycles.conormalInfinityToCoefficients I).app U) ((InfinityGluing.BundleCycles.globalConormalInfinityCover I).f U)
      (Support.Projection.BundleCycles.supportCoefficientChart I U) (globalConormalInfinityToSupport I) := by
  exact @IsOpenImmersion.isPullback _ _ _ _
    ((InfinityGluing.BundleCycles.conormalInfinityToCoefficients I).app U) ((InfinityGluing.BundleCycles.globalConormalInfinityCover I).f U)
    (Support.Projection.BundleCycles.supportCoefficientChart I U) (globalConormalInfinityToSupport I)
    (globalConormalInfinityCover_isOpenImmersion I U) (Support.Projection.BundleCycles.supportCoefficientChart_isOpenImmersion I U)
    (globalConormalInfinityToSupport_on_chart I U) (globalConormalInfinityToSupport_preimage I U)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.InfinitySupport.BundleCycles
