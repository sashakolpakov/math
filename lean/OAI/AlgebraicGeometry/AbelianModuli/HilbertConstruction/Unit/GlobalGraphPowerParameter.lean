import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Unit.PolarizationOpenCharts
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Fixed.DualGraphPowerLocality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.UnramifiedProjectiveGlobalDual
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TranslationKernelUnramifiedOpen
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.LocusPresentation

/-! # Global Graph Power Parameter -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Unit.GlobalGraphPowerParameter

noncomputable section

/-! On the first-cohomology and unramified-kernel locus, the constructed
dual and unit-division charts represent the original graph-power
enhancement predicate on every test scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

theorem unitGlobalGraphPowerLocus_nonempty
    {R : Type} [CommRing R]
    (M : Over (Spec (.of R))) [IsNoetherian M.left] {g N : ℕ}
    (F : Level.Data.AbelianSchemeWithFullLevel g N M.left)
    (P : Projective.ProjectivePresentations.ProjectivePresentation F.abelian.scheme)
    (hH1 : F.abelian.HasFieldStructureH1Bound)
    (hK : FormallyUnramified
      (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily F.abelian P.ampleLineBundle P).hom)
    (d : ℕ) (hd : 0 < d) (δ : Fin g → ℕ) (hδ : ∀ i, 0 < δ i)
    (hunit : IsUnit ((2 * d : ℕ) : Γ(M.left, ⊤))) :
    Nonempty (GraphPower.LocusPresentation.GraphPowerLocusPresentation M F P d δ) := by
  classical
  obtain ⟨D, m, _, _⟩ := UnramifiedProjectiveGlobalDual.fieldBoundLocallyNoetherianProjectiveDual_exists F.abelian P hH1 hK
  let G := GraphPower.PolarizationSubfunctor.graphPowerPolarizationSubfunctor M δ F
    (F.abelian.zeroNormalizedBundle P.ampleLineBundle) d
  have hlocal : SubfunctorOpen.SubfunctorZariskiLocalMembership G :=
    Fixed.DualGraphPowerLocality.fixedDualNormalizedGraphPower_zariskiLocalMembership M F P P.ampleLineBundle D m d hd δ hδ
  have hcharts (j : M.left.affineOpenCover.I₀) :
      Nonempty (SubfunctorOpen.SubfunctorOpenChart G (M.left.affineOpenCover.f j)) := by
    let i := M.left.affineOpenCover.f j
    let A := F.abelian.pullback i
    let Q := P.baseChange i
    let L := P.ampleLineBundle.pullback (pullback.fst F.abelian.scheme.hom i)
    let : IsNoetherianRing (M.left.affineOpenCover.X j) :=
      Noetherian.AffineGluing.affineCoverCoordinateRing_noetherian M.left j
    have hb : Set.range i ⊆ TranslationKernelUnramifiedOpen.translationKernelUnramifiedOpen F.abelian P.ampleLineBundle P :=
      (TranslationKernelUnramifiedOpen.translationKernelUnramifiedOpen_all_tests F.abelian P.ampleLineBundle P i).mpr
        (MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @FormallyUnramified)
          (IsPullback.of_hasPullback
            (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily F.abelian P.ampleLineBundle P).hom i) hK)
    have hKi : FormallyUnramified (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A Q.ampleLineBundle Q).hom :=
      TranslationKernelUnramifiedOpen.projectiveTranslationKernel_unramified_of_range_subset F.abelian P i hb
    obtain ⟨Di, mi, hmi, ⟨ei⟩⟩ :=
      UnramifiedProjectiveGlobalDual.fieldBoundLocallyNoetherianProjectiveDual_exists A Q (hH1.pullback i) hKi
    have hline : Line.Bundles.LineBundle.classOf Q.ampleLineBundle = Line.Bundles.LineBundle.classOf L :=
      Quotient.sound ⟨P.baseChangeTwistingBundleIso i⟩
    have hdiff := TranslationKernelComparison.relativeDifference_class_eq_of_lineClass (A := A) Q.ampleLineBundle L hline
    let e : (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A Q.ampleLineBundle).sheaf ≅
        (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L).sheaf := Classical.choice (Quotient.exact hdiff)
    have hLi : L.IsAmple := Q.ampleLineBundle_isAmple.of_iso (P.baseChangeTwistingBundleIso i)
    exact ⟨@PolarizationOpenCharts.unitNormalizedGraphPowerOpenChart (Spec (.of R)) M g N F P
      P.ampleLineBundle d hd δ hδ (M.left.affineOpenCover.X j)
      (M.left.affineOpenCover.X j).commRing (Noetherian.AffineGluing.affineCoverCoordinateRing_noetherian M.left j)
      i hLi Di mi hmi (Abelian.Schemes.level_unit_under_base_change i (2 * d) hunit) (ei ≪≫ e)⟩
  let C (j : M.left.affineOpenCover.I₀) := (hcharts j).some
  exact ⟨{
    parameter := SubfunctorOpen.SubfunctorOpenGluing.parameterOver G hlocal M.left.affineOpenCover.openCover C
    inclusion := SubfunctorOpen.SubfunctorOpenGluing.inclusion G hlocal M.left.affineOpenCover.openCover C
    inclusion_left_mono :=
      SubfunctorOpen.SubfunctorOpenGluing.parameter_mono G hlocal M.left.affineOpenCover.openCover C
    inclusion_locallyOfFiniteType :=
      SubfunctorOpen.SubfunctorOpenGluing.inclusion_locallyOfFiniteType G hlocal M.left.affineOpenCover.openCover C
    inclusion_quasiCompact :=
      SubfunctorOpen.SubfunctorOpenGluing.inclusion_quasiCompact G hlocal M.left.affineOpenCover.openCover C
    lifts_iff := fun T x =>
      (SubfunctorOpen.SubfunctorOpenGluing.lifts_iff G hlocal M.left.affineOpenCover.openCover C T x).symm
  }⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Unit.GlobalGraphPowerParameter
