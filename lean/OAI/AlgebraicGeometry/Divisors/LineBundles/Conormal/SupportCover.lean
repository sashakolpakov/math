import OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.DiagramGluing
import OAI.AlgebraicGeometry.Divisors.LineBundles.Support.Projection

/-! # Support Cover -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.SupportCover.BundleCycles

noncomputable section

section

/-! # LineBundleCycles: the actual conormal symmetric spectrum projects to the closed center -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite

variable {X : Scheme.{0}} (I : X.IdealSheafData)

/-- The constants map from a conormal spectrum chart to its coefficient spectrum. -/
def conormalChartProjection (U : X.AffineZariskiSite) :
    (DiagramGluing.BundleCycles.globalConormalSpectrumCover I).X U ⟶ Spec ((Support.CoefficientDiagram.BundleCycles.supportCoefficientDiagram I).obj (.op U)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (Γ(X, U.1) ⧸ I.ideal U)
    (SymmetricAlgebra (Γ(X, U.1) ⧸ I.ideal U) (I.ideal U).Cotangent)))

/-- The chart projection regarded as a map to the whole closed support. -/
def conormalChartToSupport (U : X.AffineZariskiSite) :
    (DiagramGluing.BundleCycles.globalConormalSpectrumCover I).X U ⟶ I.subscheme :=
  conormalChartProjection I U ≫ Support.Projection.BundleCycles.supportCoefficientChart I U

theorem conormalChartToSupport_toBase (U : X.AffineZariskiSite) :
    conormalChartToSupport I U ≫ I.subschemeι =
      (DiagramGluing.BundleCycles.conormalSymmetricGlueData I).natTrans.app U ≫ U.1.ι := by
  let a : Γ(X, U.1) ⟶ (Support.CoefficientDiagram.BundleCycles.supportCoefficientDiagram I).obj (.op U) :=
    CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U))
  let b : (Support.CoefficientDiagram.BundleCycles.supportCoefficientDiagram I).obj (.op U) ⟶
      (SymmetricDiagram.BundleCycles.conormalSymmetricDiagram I).obj (.op U) :=
    CommRingCat.ofHom (algebraMap (Γ(X, U.1) ⧸ I.ideal U)
      (SymmetricAlgebra (Γ(X, U.1) ⧸ I.ideal U) (I.ideal U).Cotangent))
  have hab : a ≫ b = (SymmetricDiagram.BundleCycles.conormalSymmetricDiagramMap I).app (.op U) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    rfl
  have hP : Support.Projection.BundleCycles.supportCoefficientChart I U ≫ I.subschemeι =
      (Spec.map a ≫ U.2.isoSpec.inv) ≫ U.1.ι := I.subschemeCover_map_subschemeι U
  have hspec : Spec.map b ≫ Spec.map a =
      Spec.map ((SymmetricDiagram.BundleCycles.conormalSymmetricDiagramMap I).app (.op U)) :=
    (Spec.map_comp a b).symm.trans (congrArg Spec.map hab)
  change (Spec.map b ≫ Support.Projection.BundleCycles.supportCoefficientChart I U) ≫ I.subschemeι =
    (Spec.map ((SymmetricDiagram.BundleCycles.conormalSymmetricDiagramMap I).app (.op U)) ≫ U.2.isoSpec.inv) ≫ U.1.ι
  rw [Category.assoc, hP, ← Category.assoc, ← Category.assoc, hspec]
  rfl

/-- The chart maps to the support agree on every affine transition. -/
def conormalProjectionCocone : Cocone (DiagramGluing.BundleCycles.conormalSymmetricGlueData I).functor where
  pt := I.subscheme
  ι.app U := conormalChartToSupport I U
  ι.naturality {U V} f := by
    apply (cancel_mono I.subschemeι).mp
    have h : (DiagramGluing.BundleCycles.conormalSymmetricGlueData I).functor.map f ≫
        ((DiagramGluing.BundleCycles.conormalSymmetricGlueData I).natTrans.app V ≫ V.1.ι) =
      (DiagramGluing.BundleCycles.conormalSymmetricGlueData I).natTrans.app U ≫ U.1.ι :=
      (((DiagramGluing.BundleCycles.conormalSymmetricGlueData I).natTrans ≫
        (directedCover X).functorOfLocallyDirectedHomBase).naturality f).trans (Category.comp_id _)
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => (DiagramGluing.BundleCycles.conormalSymmetricGlueData I).functor.map f ≫ k)
        (conormalChartToSupport_toBase I V)).trans
      (h.trans ((conormalChartToSupport_toBase I U).symm.trans
        (congrArg (fun k => k ≫ I.subschemeι)
          (Category.comp_id (conormalChartToSupport I U)).symm))))

/-- The actual structural projection to the closed support scheme. -/
def globalConormalToSupport : DiagramGluing.BundleCycles.globalConormalSpectrum I ⟶ I.subscheme :=
  colimit.desc _ (conormalProjectionCocone I)

theorem globalConormalToSupport_on_chart (U : X.AffineZariskiSite) :
    (DiagramGluing.BundleCycles.globalConormalSpectrumCover I).f U ≫ globalConormalToSupport I =
      conormalChartToSupport I U :=
  colimit.ι_desc (conormalProjectionCocone I) U

theorem globalConormalToSupport_toBase :
    globalConormalToSupport I ≫ I.subschemeι = DiagramGluing.BundleCycles.globalConormalSpectrumProjection I := by
  apply (DiagramGluing.BundleCycles.globalConormalSpectrumCover I).hom_ext
  intro U
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ I.subschemeι) (globalConormalToSupport_on_chart I U)).trans
    ((conormalChartToSupport_toBase I U).trans
      ((DiagramGluing.BundleCycles.conormalSymmetricGlueData I).ι_toBase U).symm))

end

/-! # LineBundleCycles: affine opens covering the closed center cover its actual conormal spectrum -/

open _root_.AlgebraicGeometry _root_.CategoryTheory
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite

variable {X : Scheme.{0}} (I : X.IdealSheafData)

instance globalConormalSpectrumCover_isOpenImmersion (U : X.AffineZariskiSite) :
    IsOpenImmersion ((DiagramGluing.BundleCycles.globalConormalSpectrumCover I).f U) := (DiagramGluing.BundleCycles.globalConormalSpectrumCover I).map_prop U

theorem globalConormalSpectrumProjection_preimage (U : X.AffineZariskiSite) :
    DiagramGluing.BundleCycles.globalConormalSpectrumProjection I ⁻¹ᵁ U.1 = ((DiagramGluing.BundleCycles.globalConormalSpectrumCover I).f U).opensRange := by
  have h := (DiagramGluing.BundleCycles.conormalSymmetricGlueData I).toBase_preimage_eq_opensRange_ι U
  change DiagramGluing.BundleCycles.globalConormalSpectrumProjection I ⁻¹ᵁ U.1.ι.opensRange =
    ((DiagramGluing.BundleCycles.globalConormalSpectrumCover I).f U).opensRange at h
  rw [Scheme.Opens.opensRange_ι] at h
  exact h

theorem globalConormalToSupport_preimage (U : X.AffineZariskiSite) :
    globalConormalToSupport I ⁻¹ᵁ (Support.Projection.BundleCycles.supportCoefficientChart I U).opensRange =
      ((DiagramGluing.BundleCycles.globalConormalSpectrumCover I).f U).opensRange := by
  rw [Support.Projection.BundleCycles.supportCoefficientChart_range, ← Scheme.Hom.comp_preimage,
    globalConormalToSupport_toBase, globalConormalSpectrumProjection_preimage]

variable {κ : Type} (U : κ → X.AffineZariskiSite)
    (hU : ∀ x : I.subscheme, ∃ i, I.subschemeι x ∈ (U i).1)

include hU in
theorem conormalSupportCharts_cover (x : DiagramGluing.BundleCycles.globalConormalSpectrum I) :
    ∃ i, ∃ y : (DiagramGluing.BundleCycles.globalConormalSpectrumCover I).X (U i), (DiagramGluing.BundleCycles.globalConormalSpectrumCover I).f (U i) y = x := by
  obtain ⟨i, hi⟩ := hU (globalConormalToSupport I x)
  have he : I.subschemeι (globalConormalToSupport I x) = DiagramGluing.BundleCycles.globalConormalSpectrumProjection I x :=
    congrArg (fun f => f x) (globalConormalToSupport_toBase I)
  have hx : x ∈ DiagramGluing.BundleCycles.globalConormalSpectrumProjection I ⁻¹ᵁ (U i).1 := by
    change DiagramGluing.BundleCycles.globalConormalSpectrumProjection I x ∈ (U i).1
    exact he ▸ hi
  rw [globalConormalSpectrumProjection_preimage] at hx
  obtain ⟨y, hy⟩ := hx
  exact ⟨i, y, hy⟩

def conormalSupportCover : (DiagramGluing.BundleCycles.globalConormalSpectrum I).OpenCover :=
  Scheme.Cover.mkOfCovers κ (fun i => (DiagramGluing.BundleCycles.globalConormalSpectrumCover I).X (U i))
    (fun i => (DiagramGluing.BundleCycles.globalConormalSpectrumCover I).f (U i)) (conormalSupportCharts_cover I U hU)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.SupportCover.BundleCycles
