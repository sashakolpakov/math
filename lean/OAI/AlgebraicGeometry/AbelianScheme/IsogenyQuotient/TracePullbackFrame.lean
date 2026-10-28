import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.GlobalTraceSection
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.DegreeBaseChange

/-! # Trace Pullback Frame -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TracePullbackFrame.Construction

noncomputable section

/-! In characteristic zero, the trace of a pulled-back frame is a
frame. Positivity and invertibility of the local degree are derived
from surjectivity and the map to the field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {X Y : Scheme.{u}} (q : X ⟶ Y)
  [IsFinite q] [Flat q] [Surjective q] [LocallyOfFinitePresentation q]
  (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y)

omit [IsFinite q] [Flat q] [Surjective q] [LocallyOfFinitePresentation q] in
set_option backward.isDefEq.respectTransparency false in
theorem localTraceSection_pullback_frame_coordinate (U : LocalTraceSections.Construction.TraceFrameOpen q L)
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ⟶ L.sheaf) [IsIso s] :
    AbelianModuli.HilbertConstruction.Frame.Coordinates.frameCoordinate (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection U.2.openSet.ι s)
      (LocalTraceSections.Construction.localTraceSection q L U (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection q s)) = (U.1 : Γ(U.2.openSet.toScheme, ⊤)) := by
  let e := AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection U.2.openSet.ι s
  have hi : LocalNormSections.Construction.localNormInput U.2.openSet (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection q s) =
      AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (q ∣_ U.2.openSet) e :=
    PullbackSectionSquares.Construction.sectionPullbackSquareIso_section q (q ∣_ U.2.openSet) (q ⁻¹ᵁ U.2.openSet).ι
      U.2.openSet.ι (morphismRestrict_ι q U.2.openSet).symm s
  have ht : LocalTraceSections.Construction.localTraceSection q L U (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection q s) =
      FramedTraceSection.Construction.framedTraceSection (q ∣_ U.2.openSet) e (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (q ∣_ U.2.openSet) e) :=
    (FramedTraceSection.Construction.framedTraceSection_frame_independent (q ∣_ U.2.openSet) U.2.frame.hom e _).trans
      (congrArg (FramedTraceSection.Construction.framedTraceSection (q ∣_ U.2.openSet) e) hi)
  rw [ht, FramedTraceSection.Construction.framedTraceSection_coordinate, AbelianModuli.HilbertConstruction.Frame.Coordinates.frameCoordinate_self]
  simpa only [map_one, Fintype.card_fin, nsmul_eq_mul, mul_one] using
    Trace.Construction.schemeTrace_pullback (q ∣_ U.2.openSet) U.2.basis (1 : Γ(U.2.openSet.toScheme, ⊤))

set_option backward.isDefEq.respectTransparency false in
theorem finiteFlatTraceSection_pullback_frame_isIso
    {k : Type u} [Field k] [CharZero k] (p : Y ⟶ Spec (.of k))
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ⟶ L.sheaf) [IsIso s] :
    IsIso (GlobalTraceSection.Construction.finiteFlatTraceSection q L (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection q s)) := by
  apply (AbelianModuli.HilbertConstruction.Section.Frames.isIso_iff_sectionNonvanishing_eq_top _).mpr
  ext y
  apply iff_true_intro
  obtain ⟨U, hy⟩ := LocalTraceSections.Construction.traceFrameOpens_cover q L y
  have : IsAffine U.2.openSet.toScheme := U.2.affine
  have : IsAffine (q ⁻¹ᵁ U.2.openSet).toScheme := isAffine_of_isAffineHom (q ∣_ U.2.openSet)
  let yU : U.2.openSet.toScheme := ⟨y, hy⟩
  have hd : 0 < U.1 := by
    rw [← NormRankBasis.Construction.affine_finrank_eq_basis_card (q ∣_ U.2.openSet) U.2.basis yU,
      Scheme.Hom.finrank_of_isPullback _ _ _ _ (isPullback_morphismRestrict q U.2.openSet).flip yU]
    exact NormRankBasis.Construction.finiteFlat_surjective_rank_pos q y
  have hlocal : yU ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (LocalTraceSections.Construction.localTraceSection q L U (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection q s)) := by
    rw [AbelianModuli.HilbertConstruction.Scalar.Nonvanishing.sectionNonvanishing_frameCoordinate (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection U.2.openSet.ι s),
      localTraceSection_pullback_frame_coordinate]
    apply (U.2.openSet.toScheme.mem_basicOpen_top _ yU).mpr
    simpa only [map_natCast] using
      Relative.DegreeBaseChange.Construction.positiveNat_isUnit_on_charZero_field_scheme (U.2.openSet.ι ≫ p) U.1 hd yU
  have h := congrArg AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing
    (GlobalTraceSection.Construction.finiteFlatTraceSection_restrict q L (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection q s) U)
  rw [AbelianModuli.HilbertConstruction.Section.Nonvanishing.sectionNonvanishing_pullback] at h
  exact (congrArg (fun V : U.2.openSet.toScheme.Opens => yU ∈ V) h).mpr hlocal

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TracePullbackFrame.Construction
