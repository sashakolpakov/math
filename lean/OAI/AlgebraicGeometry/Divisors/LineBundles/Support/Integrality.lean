import OAI.AlgebraicGeometry.Divisors.LineBundles.Support.Projection

/-! # Integrality -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Support.Integrality.BundleCycles

noncomputable section

/-!
# LineBundleCycles: integrality of the deformation of an integral closed support

The coefficient spectra are genuine open subschemes of the integral support.
Their nonempty deformation charts are integral and meet above intersections
of the support charts. This proves integrality without assuming that the
ambient scheme or the closed support is smooth.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite

universe u
variable {X : Scheme.{u}} (I P : X.IdealSheafData)

/-- Discard coefficient charts that do not meet the closed support. -/
def nonemptySupportDeformationCover : (Global.SupportDeformation.BundleCycles.globalSupportDeformation I P).OpenCover :=
  Scheme.Cover.mkOfCovers
    {U : X.AffineZariskiSite // Nonempty (Spec ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U)))}
    (fun U => (Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).X U.1)
    (fun U => (Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).f U.1)
    (by
      intro x
      obtain ⟨U, y, rfl⟩ := (Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).exists_eq x
      exact ⟨⟨U, ⟨Projection.BundleCycles.supportDeformationChartProjection I P U y⟩⟩, y, rfl⟩)
    (fun U => Global.SupportDeformation.BundleCycles.globalSupportDeformationCover_isOpenImmersion I P U.1)

variable [IsIntegral P.subscheme]

/-- A nonempty coefficient chart of the integral support has an actual domain as its ring. -/
instance supportCoefficientRing_isDomain (U : X.AffineZariskiSite)
    [Nonempty (Spec ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U)))] :
    IsDomain ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U)) :=
  (affine_isIntegral_iff _).mp (isIntegral_of_isOpenImmersion (Projection.BundleCycles.supportCoefficientChart P U))

instance nonemptySupportDeformationCover_isIntegral
    (U : (nonemptySupportDeformationCover I P).I₀) :
    IsIntegral ((nonemptySupportDeformationCover I P).X U) := by
  have : Nonempty (Spec ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U.1))) := U.2
  have : IsDomain ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U.1)) := supportCoefficientRing_isDomain P U.1
  exact inferInstanceAs (IsIntegral (Spec (CommRingCat.of (Deformation.Iff.BundleCycles.deformationAlgebra (CoefficientDiagram.BundleCycles.supportCenterIdeal P I U.1)))))

instance globalSupportDeformation_isReduced : IsReduced (Global.SupportDeformation.BundleCycles.globalSupportDeformation I P) := by
  have : ∀ U, IsReduced ((nonemptySupportDeformationCover I P).X U) := fun U => by
    have := nonemptySupportDeformationCover_isIntegral I P U
    infer_instance
  exact IsReduced.of_openCover (Global.SupportDeformation.BundleCycles.globalSupportDeformation I P) (nonemptySupportDeformationCover I P)

/-- Retained deformation charts intersect because their support charts intersect. -/
theorem nonemptySupportDeformationCover_pairwise_inter :
    Pairwise (fun U V : (nonemptySupportDeformationCover I P).I₀ =>
      ¬ Disjoint ((nonemptySupportDeformationCover I P).f U).opensRange
        ((nonemptySupportDeformationCover I P).f V).opensRange) := by
  intro U V _
  have hU : ((Projection.BundleCycles.supportCoefficientChart P U.1).opensRange : Set P.subscheme).Nonempty :=
    ⟨Projection.BundleCycles.supportCoefficientChart P U.1 (Classical.choice U.2), Classical.choice U.2, rfl⟩
  have hV : ((Projection.BundleCycles.supportCoefficientChart P V.1).opensRange : Set P.subscheme).Nonempty :=
    ⟨Projection.BundleCycles.supportCoefficientChart P V.1 (Classical.choice V.2), Classical.choice V.2, rfl⟩
  obtain ⟨x, hxU, hxV⟩ := nonempty_preirreducible_inter
    (Projection.BundleCycles.supportCoefficientChart P U.1).opensRange.isOpen (Projection.BundleCycles.supportCoefficientChart P V.1).opensRange.isOpen hU hV
  obtain ⟨y, hy⟩ := Projection.BundleCycles.globalSupportDeformationToSupport_surjective I P x
  have hyU : y ∈ ((nonemptySupportDeformationCover I P).f U).opensRange := by
    change y ∈ ((Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).f U.1).opensRange
    rw [← Projection.BundleCycles.globalSupportDeformationToSupport_preimage I P U.1]
    change Projection.BundleCycles.globalSupportDeformationToSupport I P y ∈ (Projection.BundleCycles.supportCoefficientChart P U.1).opensRange
    exact hy.symm ▸ hxU
  have hyV : y ∈ ((nonemptySupportDeformationCover I P).f V).opensRange := by
    change y ∈ ((Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).f V.1).opensRange
    rw [← Projection.BundleCycles.globalSupportDeformationToSupport_preimage I P V.1]
    change Projection.BundleCycles.globalSupportDeformationToSupport I P y ∈ (Projection.BundleCycles.supportCoefficientChart P V.1).opensRange
    exact hy.symm ▸ hxV
  intro hd
  exact Set.disjoint_left.mp (Opens.coe_disjoint.mpr hd) hyU hyV

/-- The global deformation of an actual integral support is integral. -/
instance globalSupportDeformation_isIntegral : IsIntegral (Global.SupportDeformation.BundleCycles.globalSupportDeformation I P) := by
  have hpre : ∀ U : (nonemptySupportDeformationCover I P).I₀,
      IsPreirreducible (((nonemptySupportDeformationCover I P).f U).opensRange :
        Set (Global.SupportDeformation.BundleCycles.globalSupportDeformation I P)) := by
    intro U
    have := nonemptySupportDeformationCover_isIntegral I P U
    have h := (IrreducibleSpace.isIrreducible_univ ((nonemptySupportDeformationCover I P).X U)).2.image
      ((nonemptySupportDeformationCover I P).f U)
      ((nonemptySupportDeformationCover I P).f U).continuous.continuousOn
    simp only [Set.image_univ] at h
    exact h
  have : PreirreducibleSpace (Global.SupportDeformation.BundleCycles.globalSupportDeformation I P) := ⟨IsPreirreducible.of_subset_iUnion
    (nonemptySupportDeformationCover_pairwise_inter I P) hpre isOpen_univ (by
      change Set.univ ⊆ ⋃ U, Set.range ((nonemptySupportDeformationCover I P).f U)
      rw [(nonemptySupportDeformationCover I P).iUnion_range])⟩
  have : Nonempty (Global.SupportDeformation.BundleCycles.globalSupportDeformation I P) := by
    obtain ⟨y, _⟩ := Projection.BundleCycles.globalSupportDeformationToSupport_surjective I P
      (Classical.choice (inferInstance : Nonempty P.subscheme))
    exact ⟨y⟩
  have : IrreducibleSpace (Global.SupportDeformation.BundleCycles.globalSupportDeformation I P) :=
    { toPreirreducibleSpace := inferInstance, toNonempty := inferInstance }
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Support.Integrality.BundleCycles
