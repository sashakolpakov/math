import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.LiftGluedMap

/-! # Lift Glued Reduction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.LiftGluedReduction

noncomputable section

/-! The literal reduced source is the closed reduction of the glued
etale charts. These results identify its chart pullback squares and
its underlying topological space. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
namespace Overlap
universe u
variable {X₀ X Y₀ : Scheme.{u}} {i : X₀ ⟶ X} {f₀ : Y₀ ⟶ X₀}
  {J : Type u} (D : J → LiftOverlap.Chart i f₀)
  (hcovers : ∀ y : Y₀, ∃ a : J, y ∈ Set.range (D a).source)

theorem reduction_preimage_chart (a : J) :
    LiftGluedMap.Overlap.reduction D hcovers ⁻¹ᵁ (LiftGluedMap.Overlap.chartMap D a).opensRange = (D a).source.opensRange := by
  ext y
  change LiftGluedMap.Overlap.reduction D hcovers y ∈ Set.range (LiftGluedMap.Overlap.chartMap D a) ↔ y ∈ Set.range (D a).source
  constructor
  · intro hy
    obtain ⟨b, z, rfl⟩ := hcovers y
    obtain ⟨x, hx⟩ := hy
    have hr := congrArg (fun q : (D b).reduced ⟶ LiftGluedMap.Overlap.glued D => q z) (LiftGluedMap.Overlap.source_reduction D hcovers b)
    change LiftGluedMap.Overlap.reduction D hcovers ((D b).source z) = LiftGluedMap.Overlap.chartMap D b ((D b).reduction z) at hr
    have he : LiftGluedMap.Overlap.chartMap D b ((D b).reduction z) = LiftGluedMap.Overlap.chartMap D a x := hr.symm.trans hx.symm
    obtain ⟨w, hw, _⟩ := ((LiftOverlap.Chart.glueData D).ι_eq_iff b a ((D b).reduction z) x).mp he
    change ((D b).overlap (D a)).ι w = (D b).reduction z at hw
    have hm : (D b).reduction z ∈ (D b).overlap (D a) := by
      rw [← hw]
      exact w.2
    exact ((D b).reduction_mem_overlap (D a) z).1 hm
  · rintro ⟨z, rfl⟩
    refine ⟨(D a).reduction z, ?_⟩
    exact (congrArg (fun q : (D a).reduced ⟶ LiftGluedMap.Overlap.glued D => q z) (LiftGluedMap.Overlap.source_reduction D hcovers a)).symm

theorem reduction_chart_square (a : J) :
    IsPullback (D a).reduction (D a).source (LiftGluedMap.Overlap.chartMap D a) (LiftGluedMap.Overlap.reduction D hcovers) :=
  IsOpenImmersion.isPullback _ _ _ _ (LiftGluedMap.Overlap.source_reduction D hcovers a)
    (reduction_preimage_chart D hcovers a)

theorem reduction_surjective : Function.Surjective (LiftGluedMap.Overlap.reduction D hcovers) := by
  intro x
  obtain ⟨a, z, rfl⟩ := (LiftOverlap.Chart.glueData D).ι_jointly_surjective x
  obtain ⟨z₀, rfl⟩ := (D a).reduction.surjective z
  refine ⟨(D a).source z₀, ?_⟩
  exact congrArg (fun q : (D a).reduced ⟶ LiftGluedMap.Overlap.glued D => q z₀) (LiftGluedMap.Overlap.source_reduction D hcovers a)

instance reduction_closed : IsClosedImmersion (LiftGluedMap.Overlap.reduction D hcovers) := by
  apply (IsZariskiLocalAtTarget.iff_of_openCover (P := @IsClosedImmersion)
    (LiftOverlap.Chart.glueData D).openCover).mpr
  intro a
  change J at a
  change IsClosedImmersion (pullback.snd (LiftGluedMap.Overlap.reduction D hcovers) (LiftGluedMap.Overlap.chartMap D a))
  let hp := (reduction_chart_square D hcovers a).flip
  rw [← MorphismProperty.cancel_left_of_respectsIso
    (P := @IsClosedImmersion) hp.isoPullback.hom, hp.isoPullback_hom_snd]
  infer_instance

def reductionHomeomorph : Y₀ ≃ₜ LiftGluedMap.Overlap.glued D := by
  let : Surjective (LiftGluedMap.Overlap.reduction D hcovers) := ⟨reduction_surjective D hcovers⟩
  exact Closed.ThickeningOpens.homeomorph (LiftGluedMap.Overlap.reduction D hcovers)

end Overlap

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.LiftGluedReduction
