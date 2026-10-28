import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.DeformationTo
import OAI.AlgebraicGeometry.Divisors.LineBundles.Punctured.DeformationCharts

/-! # Deformation Punctured -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Open.DeformationPunctured.BundleCycles

noncomputable section

/-! The parameter-preserving open deformation map restricts to the actual nonvanishing locus. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y : Scheme.{0}} (i : X ⟶ Y) [IsOpenImmersion i] (I : Y.IdealSheafData)

theorem globalOpenDeformationMap_preimage_punctured :
    Global.OpenDeformationMap.BundleCycles.globalOpenDeformationMap i I ⁻¹ᵁ Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedOpen I =
      Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedOpen (I.comap i) :=
  (Scheme.preimage_basicOpen_top (Global.OpenDeformationMap.BundleCycles.globalOpenDeformationMap i I) (Global.Specialization.BundleCycles.globalDeformationParameterSection I)).trans
    (congrArg (Global.Deformation.BundleCycles.globalDeformation (I.comap i)).basicOpen (DeformationTo.BundleCycles.globalOpenDeformationMap_parameterSection i I))

theorem globalOpenPuncturedMap_range_subset :
    Set.range (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion (I.comap i) ≫ Global.OpenDeformationMap.BundleCycles.globalOpenDeformationMap i I) ⊆
      Set.range (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion I) := by
  rintro _ ⟨x, rfl⟩
  apply (congrArg (fun S => Global.OpenDeformationMap.BundleCycles.globalOpenDeformationMap i I (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion (I.comap i) x) ∈ S)
    (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedOpen I).range_ι).mpr
  exact (congrArg (fun V : (Global.Deformation.BundleCycles.globalDeformation (I.comap i)).Opens =>
    Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion (I.comap i) x ∈ V)
    (globalOpenDeformationMap_preimage_punctured i I)).mpr x.property

def globalOpenPuncturedMap : Deformation.ChowLocalization.BundleCycles.globalDeformationPunctured (I.comap i) ⟶ Deformation.ChowLocalization.BundleCycles.globalDeformationPunctured I :=
  IsOpenImmersion.lift (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion I)
    (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion (I.comap i) ≫ Global.OpenDeformationMap.BundleCycles.globalOpenDeformationMap i I)
    (globalOpenPuncturedMap_range_subset i I)

theorem globalOpenPuncturedMap_inclusion :
    globalOpenPuncturedMap i I ≫ Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion I =
      Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion (I.comap i) ≫ Global.OpenDeformationMap.BundleCycles.globalOpenDeformationMap i I :=
  IsOpenImmersion.lift_fac _ _ _

instance globalOpenPuncturedMap_open : IsOpenImmersion (globalOpenPuncturedMap i I) := by
  have h : IsOpenImmersion (globalOpenPuncturedMap i I ≫ Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion I) :=
    (congrArg (fun f => IsOpenImmersion f) (globalOpenPuncturedMap_inclusion i I)).mpr inferInstance
  exact IsOpenImmersion.of_comp (globalOpenPuncturedMap i I) (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion I)

theorem globalOpenPuncturedMap_isPullback :
    IsPullback (globalOpenPuncturedMap i I) (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion (I.comap i))
      (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion I) (Global.OpenDeformationMap.BundleCycles.globalOpenDeformationMap i I) := by
  apply IsOpenImmersion.isPullback
  · exact (globalOpenPuncturedMap_inclusion i I).symm
  · change Global.OpenDeformationMap.BundleCycles.globalOpenDeformationMap i I ⁻¹ᵁ (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedOpen I).ι.opensRange =
      (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedOpen (I.comap i)).ι.opensRange
    rw [Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι]
    exact globalOpenDeformationMap_preimage_punctured i I

theorem globalOpenPuncturedMap_projection :
    globalOpenPuncturedMap i I ≫ Punctured.DeformationCharts.BundleCycles.puncturedDeformationProjection I =
      Punctured.DeformationCharts.BundleCycles.puncturedDeformationProjection (I.comap i) ≫ i := by
  rw [Punctured.DeformationCharts.BundleCycles.puncturedDeformationProjection, ← Category.assoc, globalOpenPuncturedMap_inclusion,
    Category.assoc, DeformationTo.BundleCycles.globalOpenDeformationMap_toBase, ← Category.assoc]
  rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Open.DeformationPunctured.BundleCycles
