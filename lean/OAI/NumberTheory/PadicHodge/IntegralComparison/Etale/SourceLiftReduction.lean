import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.SourceLift
import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.LiftChartSquare

/-! # Source Lift Reduction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.SourceLiftReduction

noncomputable section

/-! The globally glued etale lift has the original source as its
exact fiber over the original closed target reduction. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
variable {X₀ X Y₀ : Scheme.{u}} (i : X₀ ⟶ X) [IsClosedImmersion i]
  (hi : IsNilpotent i.ker) (f : Y₀ ⟶ X₀) [Etale f] [IsAffineHom f]

theorem reduction_square : IsPullback (SourceLift.reduction i hi f) f (SourceLift.map i hi f) i := by
  apply Scheme.isPullback_of_openCover _ _ _ _
    (LiftOverlap.Chart.glueData (SourceLift.localChart i hi f)).openCover
  intro a
  change SourceLift.Index i f at a
  let hp := (LiftGluedReduction.Overlap.reduction_chart_square (SourceLift.localChart i hi f)
    (LiftCharts.sourceMap_covers i f) a).flip
  have h := LiftChartSquare.Charts.chart_square i f a
  change IsPullback (SourceLift.localChart i hi f a).reduction
    ((SourceLift.localChart i hi f a).source ≫ f) (SourceLift.localChart i hi f a).toBase i at h
  rw [← LiftGluedMap.Overlap.chartMap_map (SourceLift.localChart i hi f) a] at h
  change IsPullback
    (pullback.snd (LiftGluedMap.Overlap.reduction (SourceLift.localChart i hi f)
      (LiftCharts.sourceMap_covers i f)) (LiftGluedMap.Overlap.chartMap (SourceLift.localChart i hi f) a))
    (pullback.fst (LiftGluedMap.Overlap.reduction (SourceLift.localChart i hi f)
      (LiftCharts.sourceMap_covers i f)) (LiftGluedMap.Overlap.chartMap (SourceLift.localChart i hi f) a) ≫ f)
    (LiftGluedMap.Overlap.chartMap (SourceLift.localChart i hi f) a ≫ LiftGluedMap.Overlap.map (SourceLift.localChart i hi f)) i
  apply h.of_iso hp.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simpa only [Iso.refl_hom, Category.comp_id] using hp.isoPullback_hom_snd.symm
  · simpa only [Iso.refl_hom, Category.assoc, Category.comp_id] using
      congrArg (fun q => q ≫ f) hp.isoPullback_hom_fst.symm
  · simp
  · simp

def fiberIso : Y₀ ≅ pullback (SourceLift.map i hi f) i := (reduction_square i hi f).isoPullback

@[reassoc] theorem fiberIso_hom_fst : (fiberIso i hi f).hom ≫ pullback.fst _ _ = SourceLift.reduction i hi f :=
  (reduction_square i hi f).isoPullback_hom_fst

@[reassoc] theorem fiberIso_hom_snd : (fiberIso i hi f).hom ≫ pullback.snd _ _ = f :=
  (reduction_square i hi f).isoPullback_hom_snd

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.SourceLiftReduction
