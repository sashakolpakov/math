import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.LiftGlueData

/-! # Lift Glued Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.LiftGluedMap

noncomputable section

/-! The genuine etale morphism obtained by gluing the lifted charts,
together with the reduction map from the original covered source. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
namespace Overlap
universe u
variable {X₀ X Y₀ : Scheme.{u}} {i : X₀ ⟶ X} {f₀ : Y₀ ⟶ X₀}
  {J : Type u} (D : J → LiftOverlap.Chart i f₀)

abbrev glued : Scheme.{u} := (LiftOverlap.Chart.glueData D).glued
abbrev chartMap (a : J) : (D a).scheme ⟶ Overlap.glued D := (LiftOverlap.Chart.glueData D).ι a

def map : Overlap.glued D ⟶ X := by
  fapply Multicoequalizer.desc
  · exact fun a => (D a).toBase
  · rintro ⟨a, b⟩
    change ((D a).overlap (D b)).ι ≫ (D a).toBase =
      ((D a).transitionOpen (D b) ≫ ((D b).overlap (D a)).ι) ≫ (D b).toBase
    rw [LiftOverlap.Chart.transitionOpen_ι, LiftOverlap.Chart.transition_base]

@[reassoc] theorem chartMap_map (a : J) : chartMap D a ≫ map D = (D a).toBase :=
  Multicoequalizer.π_desc _ _ _ _ _

instance map_etale : Etale (map D) := by
  apply (IsZariskiLocalAtSource.iff_of_openCover (P := @Etale) (LiftOverlap.Chart.glueData D).openCover).mpr
  intro a
  change J at a
  change Etale (chartMap D a ≫ map D)
  rw [chartMap_map]
  infer_instance

def sourceCover (hcovers : ∀ y : Y₀, ∃ a : J, y ∈ Set.range (D a).source) : Y₀.OpenCover where
  I₀ := J
  X a := (D a).reduced
  f a := (D a).source
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨hcovers, inferInstance⟩

private theorem reduction_overlap_range (a b : J) :
    Set.range (pullback.fst (D a).source (D b).source ≫ (D a).reduction) ⊆
      Set.range ((D a).overlap (D b)).ι := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨z, rfl⟩
  apply ((D a).reduction_mem_overlap (D b) _).2
  refine ⟨pullback.snd (D a).source (D b).source z, ?_⟩
  exact (congrArg (fun q : pullback (D a).source (D b).source ⟶ Y₀ => q z)
    (pullback.condition (f := (D a).source) (g := (D b).source))).symm

private def reductionOverlap (a b : J) :
    pullback (D a).source (D b).source ⟶ ((D a).overlap (D b)).toScheme :=
  IsOpenImmersion.lift _ (pullback.fst _ _ ≫ (D a).reduction) (reduction_overlap_range D a b)

private theorem reductionOverlap_ι (a b : J) : reductionOverlap D a b ≫ ((D a).overlap (D b)).ι =
    pullback.fst (D a).source (D b).source ≫ (D a).reduction :=
  IsOpenImmersion.lift_fac _ _ _

private theorem reductionOverlap_transition (a b : J) :
    reductionOverlap D a b ≫ (D a).transition (D b) =
      pullback.snd (D a).source (D b).source ≫ (D b).reduction := by
  simpa only [Category.id_comp] using (D a).transition_reduction_of (D b)
    (𝟙 _) (reductionOverlap D a b) (pullback.fst _ _) (pullback.snd _ _)
    (by simpa only [Category.id_comp] using reductionOverlap_ι D a b) pullback.condition

theorem reduction_compatible (a b : J) :
    pullback.fst (D a).source (D b).source ≫ ((D a).reduction ≫ chartMap D a) =
      pullback.snd (D a).source (D b).source ≫ ((D b).reduction ≫ chartMap D b) := by
  rw [← Category.assoc, ← reductionOverlap_ι]
  have hg := (LiftOverlap.Chart.glueData D).glue_condition a b
  change (D a).transitionOpen (D b) ≫ ((D b).overlap (D a)).ι ≫ chartMap D b =
    ((D a).overlap (D b)).ι ≫ chartMap D a at hg
  rw [Category.assoc, ← hg, LiftOverlap.Chart.transitionOpen_ι_assoc,
    ← Category.assoc, reductionOverlap_transition, Category.assoc]

def reduction (hcovers : ∀ y : Y₀, ∃ a : J, y ∈ Set.range (D a).source) : Y₀ ⟶ Overlap.glued D :=
  (sourceCover D hcovers).glueMorphisms (fun a => (D a).reduction ≫ chartMap D a)
    (reduction_compatible D)

@[reassoc] theorem source_reduction (hcovers : ∀ y : Y₀, ∃ a : J, y ∈ Set.range (D a).source) (a : J) :
    (D a).source ≫ Overlap.reduction D hcovers = (D a).reduction ≫ chartMap D a :=
  (sourceCover D hcovers).ι_glueMorphisms _ _ a

theorem reduction_map (hcovers : ∀ y : Y₀, ∃ a : J, y ∈ Set.range (D a).source) :
    Overlap.reduction D hcovers ≫ map D = f₀ ≫ i := by
  apply (sourceCover D hcovers).hom_ext
  intro a
  change (D a).source ≫ (Overlap.reduction D hcovers ≫ map D) = (D a).source ≫ f₀ ≫ i
  rw [← Category.assoc, source_reduction, Category.assoc, chartMap_map]
  exact (D a).over

end Overlap

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.LiftGluedMap
