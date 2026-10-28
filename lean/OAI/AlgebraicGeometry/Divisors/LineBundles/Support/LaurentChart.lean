import OAI.AlgebraicGeometry.Divisors.LineBundles.Punctured.DeformationCharts
import OAI.AlgebraicGeometry.Divisors.LineBundles.Support.Specialization

/-! # Laurent Chart -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Support.LaurentChart.BundleCycles

noncomputable section

section

/-! # LineBundleCycles: the actual punctured deformation of a closed support -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X : Scheme.{0}} (I P : X.IdealSheafData)

def supportPuncturedOpen : (Global.SupportDeformation.BundleCycles.globalSupportDeformation I P).Opens :=
  Global.SupportDeformation.BundleCycles.globalSupportDeformationMap I P ⁻¹ᵁ Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedOpen I

theorem supportPuncturedOpen_eq :
    supportPuncturedOpen I P =
      (Global.SupportDeformation.BundleCycles.globalSupportDeformation I P).basicOpen (Specialization.BundleCycles.globalSupportParameterSection I P) :=
  Scheme.preimage_basicOpen_top (Global.SupportDeformation.BundleCycles.globalSupportDeformationMap I P) (Global.Specialization.BundleCycles.globalDeformationParameterSection I)

def supportPuncturedDeformation : Scheme := (supportPuncturedOpen I P).toScheme

def supportPuncturedInclusion : supportPuncturedDeformation I P ⟶ Global.SupportDeformation.BundleCycles.globalSupportDeformation I P :=
  (supportPuncturedOpen I P).ι

instance supportPuncturedInclusion_openImmersion : IsOpenImmersion (supportPuncturedInclusion I P) :=
  inferInstanceAs (IsOpenImmersion (supportPuncturedOpen I P).ι)

def supportPuncturedMap : supportPuncturedDeformation I P ⟶ Deformation.ChowLocalization.BundleCycles.globalDeformationPunctured I :=
  Global.SupportDeformation.BundleCycles.globalSupportDeformationMap I P ∣_ Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedOpen I

instance supportPuncturedMap_closedImmersion : IsClosedImmersion (supportPuncturedMap I P) :=
  inferInstanceAs (IsClosedImmersion (Global.SupportDeformation.BundleCycles.globalSupportDeformationMap I P ∣_ Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedOpen I))

theorem supportPuncturedMap_inclusion :
    supportPuncturedMap I P ≫ Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion I =
      supportPuncturedInclusion I P ≫ Global.SupportDeformation.BundleCycles.globalSupportDeformationMap I P :=
  morphismRestrict_ι _ _

def supportPuncturedProjection : supportPuncturedDeformation I P ⟶ P.subscheme :=
  supportPuncturedInclusion I P ≫ Projection.BundleCycles.globalSupportDeformationToSupport I P

theorem supportPuncturedMap_toBase :
    supportPuncturedMap I P ≫ Punctured.DeformationCharts.BundleCycles.puncturedDeformationProjection I =
      supportPuncturedProjection I P ≫ P.subschemeι := by
  rw [Punctured.DeformationCharts.BundleCycles.puncturedDeformationProjection, ← Category.assoc, supportPuncturedMap_inclusion,
    Category.assoc, Global.SupportDeformation.BundleCycles.globalSupportDeformationMap_toBase]
  exact (congrArg (fun k => supportPuncturedInclusion I P ≫ k)
    (Projection.BundleCycles.globalSupportDeformationToSupport_toBase I P)).symm.trans (Category.assoc _ _ _).symm

instance supportPuncturedDeformation_noetherian [AlgebraicGeometry.IsNoetherian X] :
    AlgebraicGeometry.IsNoetherian (supportPuncturedDeformation I P) := by
  have : IsLocallyNoetherian (supportPuncturedDeformation I P) :=
    LocallyOfFiniteType.isLocallyNoetherian (supportPuncturedInclusion I P)
  have : NoetherianSpace (supportPuncturedDeformation I P) :=
    (supportPuncturedInclusion I P).isOpenEmbedding.isInducing.noetherianSpace
  exact ⟨⟩

end

/-! # LineBundleCycles: actual Laurent charts of the closed-support deformation -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite

variable {X : Scheme.{0}} (I P : X.IdealSheafData) (U : X.AffineZariskiSite)

def supportLaurentChart :
    Spec (CommRingCat.of (LaurentPolynomial ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U)))) ⟶
      Global.SupportDeformation.BundleCycles.globalSupportDeformation I P :=
  Affine.PuncturedDeformation.BundleCycles.affinePuncturedDeformationMap (CoefficientDiagram.BundleCycles.supportCenterIdeal P I U) ≫ (Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).f U

instance supportLaurentChart_openImmersion : IsOpenImmersion (supportLaurentChart I P U) :=
  @IsOpenImmersion.comp _ _ _
    (show Spec (CommRingCat.of (LaurentPolynomial ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U)))) ⟶
      (Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).X U from Affine.PuncturedDeformation.BundleCycles.affinePuncturedDeformationMap (CoefficientDiagram.BundleCycles.supportCenterIdeal P I U))
    ((Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).f U)
    (Affine.PuncturedDeformation.BundleCycles.affinePuncturedDeformationMap_openImmersion (CoefficientDiagram.BundleCycles.supportCenterIdeal P I U))
    ((Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).map_prop U)

theorem supportLaurentChart_toSupport :
    supportLaurentChart I P U ≫ Projection.BundleCycles.globalSupportDeformationToSupport I P =
      Laurent.FiberGenericPoint.BundleCycles.laurentProjection ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U)) ≫ Projection.BundleCycles.supportCoefficientChart P U := by
  let l : Spec (CommRingCat.of (LaurentPolynomial ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U)))) ⟶
      (Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).X U := Affine.PuncturedDeformation.BundleCycles.affinePuncturedDeformationMap (CoefficientDiagram.BundleCycles.supportCenterIdeal P I U)
  let b := Projection.BundleCycles.supportDeformationChartProjection I P U
  exact (Category.assoc l ((Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).f U)
    (Projection.BundleCycles.globalSupportDeformationToSupport I P)).trans
      ((congrArg (fun k => l ≫ k) (Projection.BundleCycles.globalSupportDeformationToSupport_on_chart I P U)).trans
        ((Category.assoc l b (Projection.BundleCycles.supportCoefficientChart P U)).symm.trans
          (congrArg (fun k => k ≫ Projection.BundleCycles.supportCoefficientChart P U)
            (Affine.PuncturedDeformation.BundleCycles.affinePuncturedDeformationMap_toBase (CoefficientDiagram.BundleCycles.supportCenterIdeal P I U)))))

theorem supportLaurentChart_range :
    Set.range (supportLaurentChart I P U) =
      Set.range ((Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).f U) ∩
        (supportPuncturedOpen I P : Set (Global.SupportDeformation.BundleCycles.globalSupportDeformation I P)) := by
  have hb := Scheme.preimage_basicOpen_top ((Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).f U)
    (Specialization.BundleCycles.globalSupportParameterSection I P)
  rw [Specialization.BundleCycles.globalSupportParameterSection_on_chart] at hb
  have ha : Set.range (Affine.PuncturedDeformation.BundleCycles.affinePuncturedDeformationMap (CoefficientDiagram.BundleCycles.supportCenterIdeal P I U)) =
      ((Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).f U) ⁻¹'
        (supportPuncturedOpen I P : Set (Global.SupportDeformation.BundleCycles.globalSupportDeformation I P)) := by
    rw [supportPuncturedOpen_eq]
    exact (Affine.PuncturedDeformation.BundleCycles.affinePuncturedDeformationMap_range (CoefficientDiagram.BundleCycles.supportCenterIdeal P I U)).trans
      (congrArg (fun V : ((Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).X U).Opens =>
        (V : Set ((Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).X U))) hb).symm
  let c : (Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).X U → Global.SupportDeformation.BundleCycles.globalSupportDeformation I P :=
    (Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).f U
  let l : Spec (CommRingCat.of (LaurentPolynomial ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U)))) →
      (Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).X U := Affine.PuncturedDeformation.BundleCycles.affinePuncturedDeformationMap (CoefficientDiagram.BundleCycles.supportCenterIdeal P I U)
  exact (Set.range_comp c l).trans ((congrArg (Set.image c) ha).trans Set.image_preimage_eq_range_inter)

theorem supportLaurentChart_range_subset :
    Set.range (supportLaurentChart I P U) ⊆ Set.range (supportPuncturedInclusion I P) := by
  rw [supportLaurentChart_range]
  exact fun _ hx => (supportPuncturedOpen I P).range_ι.symm ▸ hx.2

def supportPuncturedLaurentChart :
    Spec (CommRingCat.of (LaurentPolynomial ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U)))) ⟶
      supportPuncturedDeformation I P :=
  IsOpenImmersion.lift (supportPuncturedInclusion I P) (supportLaurentChart I P U)
    (supportLaurentChart_range_subset I P U)

theorem supportPuncturedLaurentChart_inclusion :
    supportPuncturedLaurentChart I P U ≫ supportPuncturedInclusion I P = supportLaurentChart I P U :=
  IsOpenImmersion.lift_fac _ _ _

instance supportPuncturedLaurentChart_openImmersion : IsOpenImmersion (supportPuncturedLaurentChart I P U) := by
  have h : IsOpenImmersion (supportPuncturedLaurentChart I P U ≫ supportPuncturedInclusion I P) :=
    (congrArg (fun f => IsOpenImmersion f) (supportPuncturedLaurentChart_inclusion I P U)).mpr inferInstance
  exact IsOpenImmersion.of_comp (supportPuncturedLaurentChart I P U) (supportPuncturedInclusion I P)

theorem supportPuncturedLaurentChart_toSupport :
    supportPuncturedLaurentChart I P U ≫ supportPuncturedProjection I P =
      Laurent.FiberGenericPoint.BundleCycles.laurentProjection ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U)) ≫ Projection.BundleCycles.supportCoefficientChart P U := by
  rw [supportPuncturedProjection, ← Category.assoc, supportPuncturedLaurentChart_inclusion]
  exact supportLaurentChart_toSupport I P U

theorem supportPuncturedLaurentChart_range :
    Set.range (supportPuncturedLaurentChart I P U) =
      supportPuncturedProjection I P ⁻¹' Set.range (Projection.BundleCycles.supportCoefficientChart P U) := by
  rw [Open.LiftRange.BundleCycles.range_openLift (supportPuncturedInclusion I P) (supportLaurentChart I P U)
    (supportPuncturedLaurentChart I P U) (supportPuncturedLaurentChart_inclusion I P U),
    supportLaurentChart_range, Set.preimage_inter]
  have hopen : (supportPuncturedInclusion I P) ⁻¹'
      (supportPuncturedOpen I P : Set (Global.SupportDeformation.BundleCycles.globalSupportDeformation I P)) = Set.univ := by
    change (supportPuncturedOpen I P).ι ⁻¹' (supportPuncturedOpen I P : Set (Global.SupportDeformation.BundleCycles.globalSupportDeformation I P)) = _
    rw [← (supportPuncturedOpen I P).range_ι, Set.preimage_range]
    rfl
  rw [hopen, Set.inter_univ]
  exact congrArg (Set.preimage (supportPuncturedInclusion I P))
    (congrArg (fun V : (Global.SupportDeformation.BundleCycles.globalSupportDeformation I P).Opens => (V : Set (Global.SupportDeformation.BundleCycles.globalSupportDeformation I P)))
      (Projection.BundleCycles.globalSupportDeformationToSupport_preimage I P U)).symm

omit U in
theorem supportPuncturedLaurentChart_covers (y : supportPuncturedDeformation I P) :
    ∃ U : X.AffineZariskiSite, y ∈ Set.range (supportPuncturedLaurentChart I P U) := by
  obtain ⟨U, p, hp⟩ := P.subschemeCover.openCover.exists_eq (supportPuncturedProjection I P y)
  refine ⟨U, ?_⟩
  exact (congrArg (fun s : Set (supportPuncturedDeformation I P) => y ∈ s)
    (supportPuncturedLaurentChart_range I P U)).mpr ⟨p, hp⟩

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Support.LaurentChart.BundleCycles
