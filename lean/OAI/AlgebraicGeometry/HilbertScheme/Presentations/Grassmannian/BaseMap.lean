import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.OverlapBaseChange
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Grassmannian.Gluing

/-! # Base Map -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Grassmannian.BaseMap

noncomputable section

/-! The actual glued Grassmannian is functorial in its base scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {ι ν : Type u} [Fintype ι] [DecidableEq ι]
variable {S T : Scheme.{u}} (f : T ⟶ S)

theorem normalizedChartBaseMaps_glue (a b : ι → ν) :
    (Normalized.Overlap.Grassmannian.normalizedOverlapInclusion a b T).left ≫
        (Normalized.ChartBaseChange.Grassmannian.normalizedChartBaseMap a f ≫ Gluing.grassmannianChartMap a S) =
      ((Normalized.Overlap.Grassmannian.normalizedOverlapTransition a b T).hom.left ≫ (Normalized.Overlap.Grassmannian.normalizedOverlapInclusion b a T).left) ≫
        (Normalized.ChartBaseChange.Grassmannian.normalizedChartBaseMap b f ≫ Gluing.grassmannianChartMap b S) := by
  have hS := ((Gluing.normalizedGrassmannianGlueData (ι := ι) (ν := ν) S).glue_condition a b).symm
  change (Normalized.Overlap.Grassmannian.normalizedOverlapInclusion a b S).left ≫ Gluing.grassmannianChartMap a S =
    (Normalized.Overlap.Grassmannian.normalizedOverlapTransition a b S).hom.left ≫
      (Normalized.Overlap.Grassmannian.normalizedOverlapInclusion b a S).left ≫ Gluing.grassmannianChartMap b S at hS
  rw [← Category.assoc, ← Normalized.OverlapBaseChange.Grassmannian.normalizedOverlapBaseMap_inclusion, Category.assoc, hS,
    ← Category.assoc (Normalized.OverlapBaseChange.Grassmannian.normalizedOverlapBaseMap a b f), Normalized.OverlapBaseChange.Grassmannian.normalizedOverlapBaseMap_transition]
  simp only [Category.assoc]
  rw [← Category.assoc (Normalized.OverlapBaseChange.Grassmannian.normalizedOverlapBaseMap b a f), Normalized.OverlapBaseChange.Grassmannian.normalizedOverlapBaseMap_inclusion]
  simp only [Category.assoc]

def grassmannianBaseMap : Gluing.grassmannianScheme (ι := ι) (ν := ν) T ⟶
    Gluing.grassmannianScheme (ι := ι) (ν := ν) S := by
  fapply Multicoequalizer.desc
  · exact fun a => Normalized.ChartBaseChange.Grassmannian.normalizedChartBaseMap a f ≫ Gluing.grassmannianChartMap a S
  rintro ⟨a, b⟩
  exact normalizedChartBaseMaps_glue f a b

theorem grassmannianBaseMap_chart (a : ι → ν) :
    Gluing.grassmannianChartMap a T ≫ grassmannianBaseMap f =
      Normalized.ChartBaseChange.Grassmannian.normalizedChartBaseMap a f ≫ Gluing.grassmannianChartMap a S :=
  Multicoequalizer.π_desc _ _ _ _ _

theorem grassmannianBaseMap_over :
    grassmannianBaseMap (ι := ι) (ν := ν) f ≫ Gluing.grassmannianStructureMap S =
      Gluing.grassmannianStructureMap T ≫ f := by
  apply (Gluing.normalizedGrassmannianGlueData (ι := ι) (ν := ν) T).openCover.hom_ext
  intro a
  change ι → ν at a
  change Gluing.grassmannianChartMap a T ≫
    (grassmannianBaseMap f ≫ Gluing.grassmannianStructureMap S) =
      Gluing.grassmannianChartMap a T ≫ (Gluing.grassmannianStructureMap T ≫ f)
  rw [← Category.assoc, grassmannianBaseMap_chart, Category.assoc,
    Gluing.grassmannianChartMap_structureMap, Normalized.ChartBaseChange.Grassmannian.normalizedChartBaseMap_over,
    ← Category.assoc, Gluing.grassmannianChartMap_structureMap]

theorem grassmannianBaseMap_id : grassmannianBaseMap (ι := ι) (ν := ν) (𝟙 S) = 𝟙 _ := by
  apply (Gluing.normalizedGrassmannianGlueData (ι := ι) (ν := ν) S).openCover.hom_ext
  intro a
  change ι → ν at a
  change Gluing.grassmannianChartMap a S ≫ grassmannianBaseMap (𝟙 S) = Gluing.grassmannianChartMap a S ≫ 𝟙 _
  rw [grassmannianBaseMap_chart, Normalized.ChartBaseChange.Grassmannian.normalizedChartBaseMap_id, Category.id_comp, Category.comp_id]

theorem grassmannianBaseMap_comp {U : Scheme.{u}} (g : U ⟶ T) :
    grassmannianBaseMap (ι := ι) (ν := ν) (g ≫ f) = grassmannianBaseMap g ≫ grassmannianBaseMap f := by
  apply (Gluing.normalizedGrassmannianGlueData (ι := ι) (ν := ν) U).openCover.hom_ext
  intro a
  change ι → ν at a
  change Gluing.grassmannianChartMap a U ≫ grassmannianBaseMap (g ≫ f) =
    Gluing.grassmannianChartMap a U ≫ (grassmannianBaseMap g ≫ grassmannianBaseMap f)
  rw [grassmannianBaseMap_chart, Normalized.ChartBaseChange.Grassmannian.normalizedChartBaseMap_comp, Category.assoc,
    ← grassmannianBaseMap_chart, ← Category.assoc, ← grassmannianBaseMap_chart, Category.assoc]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Grassmannian.BaseMap
