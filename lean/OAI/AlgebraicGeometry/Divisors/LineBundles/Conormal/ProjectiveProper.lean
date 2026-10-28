import OAI.AlgebraicGeometry.Divisors.LineBundles.GlobalConormal.Compactification
import OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.SupportCover

/-! # Projective Proper -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.ProjectiveProper.BundleCycles

noncomputable section

section

/-! The actual projective conormal construction and its affine open
have compatible projections to the closed center. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite

variable {X : Scheme.{0}} (I : X.IdealSheafData)

def conormalProjectiveChartToSupport (U : X.AffineZariskiSite) : ProjectiveDiagram.BundleCycles.conormalProjectiveChart I U ⟶ I.subscheme :=
  (ProjectiveGluing.BundleCycles.conormalProjectiveToCoefficients I).app U ≫ Support.Projection.BundleCycles.supportCoefficientChart I U

theorem conormalProjectiveChartToSupport_toBase (U : X.AffineZariskiSite) :
    conormalProjectiveChartToSupport I U ≫ I.subschemeι =
      (ProjectiveGluing.BundleCycles.conormalProjectiveGlueData I).natTrans.app U ≫ U.1.ι := by
  let q := CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U))
  have hq : Support.Projection.BundleCycles.supportCoefficientChart I U ≫ I.subschemeι =
      (Spec.map q ≫ U.2.isoSpec.inv) ≫ U.1.ι := I.subschemeCover_map_subschemeι U
  change ((ProjectiveGluing.BundleCycles.conormalProjectiveToCoefficients I).app U ≫ Support.Projection.BundleCycles.supportCoefficientChart I U) ≫ I.subschemeι =
    ((ProjectiveGluing.BundleCycles.conormalProjectiveToCoefficients I).app U ≫ (Spec.map q ≫ U.2.isoSpec.inv)) ≫ U.1.ι
  rw [Category.assoc, hq]
  simp only [Category.assoc]
  rfl

def conormalProjectiveSupportCocone : Cocone (ProjectiveGluing.BundleCycles.conormalProjectiveGlueData I).functor where
  pt := I.subscheme
  ι.app U := conormalProjectiveChartToSupport I U
  ι.naturality {U V} f := by
    apply (cancel_mono I.subschemeι).mp
    have h : (ProjectiveGluing.BundleCycles.conormalProjectiveGlueData I).functor.map f ≫
        ((ProjectiveGluing.BundleCycles.conormalProjectiveGlueData I).natTrans.app V ≫ V.1.ι) =
      (ProjectiveGluing.BundleCycles.conormalProjectiveGlueData I).natTrans.app U ≫ U.1.ι :=
      (((ProjectiveGluing.BundleCycles.conormalProjectiveGlueData I).natTrans ≫
        (directedCover X).functorOfLocallyDirectedHomBase).naturality f).trans (Category.comp_id _)
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => (ProjectiveGluing.BundleCycles.conormalProjectiveGlueData I).functor.map f ≫ k)
        (conormalProjectiveChartToSupport_toBase I V)).trans
      (h.trans ((conormalProjectiveChartToSupport_toBase I U).symm.trans
        (congrArg (fun k => k ≫ I.subschemeι)
          (Category.comp_id (conormalProjectiveChartToSupport I U)).symm))))

def globalConormalProjectiveToSupport : ProjectiveGluing.BundleCycles.globalConormalProjective I ⟶ I.subscheme :=
  colimit.desc _ (conormalProjectiveSupportCocone I)

theorem globalConormalProjectiveToSupport_on_chart (U : X.AffineZariskiSite) :
    (ProjectiveGluing.BundleCycles.globalConormalProjectiveCover I).f U ≫ globalConormalProjectiveToSupport I =
      conormalProjectiveChartToSupport I U := colimit.ι_desc (conormalProjectiveSupportCocone I) U

theorem globalConormalProjectiveToSupport_toBase :
    globalConormalProjectiveToSupport I ≫ I.subschemeι = ProjectiveGluing.BundleCycles.globalConormalProjectiveToBase I := by
  apply (ProjectiveGluing.BundleCycles.globalConormalProjectiveCover I).hom_ext
  intro U
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ I.subschemeι) (globalConormalProjectiveToSupport_on_chart I U)).trans
      ((conormalProjectiveChartToSupport_toBase I U).trans
        ((ProjectiveGluing.BundleCycles.conormalProjectiveGlueData I).ι_toBase U).symm))

theorem globalConormalCompactification_toSupport :
    GlobalConormal.Compactification.BundleCycles.globalConormalCompactification I ≫ globalConormalProjectiveToSupport I = SupportCover.BundleCycles.globalConormalToSupport I := by
  apply (cancel_mono I.subschemeι).mp
  rw [Category.assoc, globalConormalProjectiveToSupport_toBase, SupportCover.BundleCycles.globalConormalToSupport_toBase]
  exact GlobalConormal.Compactification.BundleCycles.globalConormalCompactification_toBase I

instance globalConormalProjectiveCover_isOpenImmersion (U : X.AffineZariskiSite) :
    IsOpenImmersion ((ProjectiveGluing.BundleCycles.globalConormalProjectiveCover I).f U) := (ProjectiveGluing.BundleCycles.globalConormalProjectiveCover I).map_prop U

theorem globalConormalProjectiveToBase_preimage (U : X.AffineZariskiSite) :
    ProjectiveGluing.BundleCycles.globalConormalProjectiveToBase I ⁻¹ᵁ U.1 = ((ProjectiveGluing.BundleCycles.globalConormalProjectiveCover I).f U).opensRange := by
  have h := (ProjectiveGluing.BundleCycles.conormalProjectiveGlueData I).toBase_preimage_eq_opensRange_ι U
  change ProjectiveGluing.BundleCycles.globalConormalProjectiveToBase I ⁻¹ᵁ U.1.ι.opensRange =
    ((ProjectiveGluing.BundleCycles.globalConormalProjectiveCover I).f U).opensRange at h
  rw [Scheme.Opens.opensRange_ι] at h
  exact h

theorem globalConormalProjectiveToSupport_preimage (U : X.AffineZariskiSite) :
    globalConormalProjectiveToSupport I ⁻¹ᵁ (Support.Projection.BundleCycles.supportCoefficientChart I U).opensRange =
      ((ProjectiveGluing.BundleCycles.globalConormalProjectiveCover I).f U).opensRange := by
  rw [Support.Projection.BundleCycles.supportCoefficientChart_range, ← Scheme.Hom.comp_preimage,
    globalConormalProjectiveToSupport_toBase, globalConormalProjectiveToBase_preimage]

theorem globalConormalProjectiveToSupport_chart_isPullback (U : X.AffineZariskiSite) :
    IsPullback ((ProjectiveGluing.BundleCycles.conormalProjectiveToCoefficients I).app U) ((ProjectiveGluing.BundleCycles.globalConormalProjectiveCover I).f U)
      (Support.Projection.BundleCycles.supportCoefficientChart I U) (globalConormalProjectiveToSupport I) := by
  exact @IsOpenImmersion.isPullback _ _ _ _
    ((ProjectiveGluing.BundleCycles.conormalProjectiveToCoefficients I).app U) ((ProjectiveGluing.BundleCycles.globalConormalProjectiveCover I).f U)
    (Support.Projection.BundleCycles.supportCoefficientChart I U) (globalConormalProjectiveToSupport I)
    (globalConormalProjectiveCover_isOpenImmersion I U) (Support.Projection.BundleCycles.supportCoefficientChart_isOpenImmersion I U)
    (globalConormalProjectiveToSupport_on_chart I U) (globalConormalProjectiveToSupport_preimage I U)

end

/-! Over a locally noetherian ambient scheme, the actual projective
conormal construction is proper over the closed center. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem cotangentQuotient_finite {R : Type} [CommRing R] [IsNoetherianRing R] (I : Ideal R) :
    Module.Finite (R ⧸ I) I.Cotangent := by
  let : Module.Finite R I.Cotangent := Module.Finite.of_surjective I.toCotangent I.toCotangent_surjective
  exact Module.Finite.of_restrictScalars_finite R (R ⧸ I) I.Cotangent

variable {X : Scheme.{0}} [hX : IsLocallyNoetherian X] (I : X.IdealSheafData)

include hX

instance globalConormalProjectiveToSupport_isProper : IsProper (globalConormalProjectiveToSupport I) := by
  apply Global.DeformationProperties.BundleCycles.morphismProperty_of_cover_pullbacks (@IsProper) (globalConormalProjectiveToSupport I)
    I.subschemeCover.openCover (ProjectiveDiagram.BundleCycles.conormalProjectiveChart I)
    (fun U => (ProjectiveGluing.BundleCycles.globalConormalProjectiveCover I).f U)
    (fun U => (ProjectiveGluing.BundleCycles.conormalProjectiveToCoefficients I).app U)
    (globalConormalProjectiveToSupport_chart_isPullback I)
  intro U
  let : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian ⟨U.1, U.2⟩
  let : Module.Finite (Γ(X, U.1) ⧸ I.ideal U) (I.ideal U).Cotangent := cotangentQuotient_finite _
  exact SymmetricProjective.Proper.BundleCycles.symmetricProjectiveToBase_isProper _ _

instance globalConormalProjectiveToBase_isProper : IsProper (ProjectiveGluing.BundleCycles.globalConormalProjectiveToBase I) := by
  rw [← globalConormalProjectiveToSupport_toBase]
  infer_instance

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.ProjectiveProper.BundleCycles
