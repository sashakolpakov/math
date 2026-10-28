import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Grassmannian.Gluing
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Finite Type -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Grassmannian.FiniteType

noncomputable section

/-! Finiteness of the Grassmannian scheme constructed from quotient charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.AlgebraicGeometry

universe u

variable {ι ν : Type u} [Fintype ι] [DecidableEq ι] [Finite ν]
variable (a : ι → ν) (S : Scheme.{u})

instance normalizedChart_isAffineHom : IsAffineHom (Normalized.Chart.Grassmannian.normalizedChart a S).hom := by
  have : IsAffineHom (Chart.matrixSpace ι ν S).hom :=
    inferInstanceAs (IsAffineHom (AffineSpace (ι × ν) S ↘ S))
  have h : IsAffineHom ((Normalized.Chart.Grassmannian.normalizedChartInclusion a S).left ≫ (Chart.matrixSpace ι ν S).hom) := inferInstance
  rwa [(Normalized.Chart.Grassmannian.normalizedChartInclusion a S).w] at h

instance normalizedChart_locallyOfFiniteType : LocallyOfFiniteType (Normalized.Chart.Grassmannian.normalizedChart a S).hom := by
  have : LocallyOfFiniteType (Chart.matrixSpace ι ν S).hom :=
    inferInstanceAs (LocallyOfFiniteType (AffineSpace (ι × ν) S ↘ S))
  have h : LocallyOfFiniteType
      ((Normalized.Chart.Grassmannian.normalizedChartInclusion a S).left ≫ (Chart.matrixSpace ι ν S).hom) := inferInstance
  rwa [(Normalized.Chart.Grassmannian.normalizedChartInclusion a S).w] at h

instance grassmannianStructureMap_locallyOfFiniteType :
    LocallyOfFiniteType (Gluing.grassmannianStructureMap (ι := ι) (ν := ν) S) := by
  have : IsZariskiLocalAtSource @LocallyOfFiniteType.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource
      (P := @LocallyOfFiniteType.{u}) (Q := RingHom.FiniteType)
  apply (IsZariskiLocalAtSource.iff_of_openCover (P := @LocallyOfFiniteType)
    (Gluing.normalizedGrassmannianGlueData (ι := ι) (ν := ν) S).openCover).mpr
  intro a
  change ι → ν at a
  change LocallyOfFiniteType
    (Gluing.grassmannianChartMap (a : ι → ν) S ≫ Gluing.grassmannianStructureMap (ι := ι) (ν := ν) S)
  rw [Gluing.grassmannianChartMap_structureMap]
  exact normalizedChart_locallyOfFiniteType a S

instance grassmannianStructureMap_quasiCompact :
    QuasiCompact (Gluing.grassmannianStructureMap (ι := ι) (ν := ν) S) := by
  apply quasiCompact_iff_forall_isAffineOpen.mpr
  intro U hU
  have heq : (Gluing.grassmannianStructureMap (ι := ι) (ν := ν) S) ⁻¹' (U : Set S) =
      ⋃ a : ι → ν, (Gluing.grassmannianChartMap a S) '' ((Normalized.Chart.Grassmannian.normalizedChart a S).hom ⁻¹' (U : Set S)) := by
    ext x
    constructor
    · intro hx
      obtain ⟨a, y, rfl⟩ := Gluing.grassmannianCharts_cover S x
      refine Set.mem_iUnion.mpr ⟨a, y, ?_, rfl⟩
      change (Normalized.Chart.Grassmannian.normalizedChart a S).hom y ∈ U
      change Gluing.grassmannianStructureMap (ι := ι) (ν := ν) S (Gluing.grassmannianChartMap a S y) ∈ U at hx
      rwa [← Scheme.Hom.comp_apply, Gluing.grassmannianChartMap_structureMap] at hx
    · intro hx
      obtain ⟨a, y, hy, rfl⟩ := Set.mem_iUnion.mp hx
      change Gluing.grassmannianStructureMap (ι := ι) (ν := ν) S (Gluing.grassmannianChartMap a S y) ∈ U
      rw [← Scheme.Hom.comp_apply, Gluing.grassmannianChartMap_structureMap]
      exact hy
  change IsCompact ((Gluing.grassmannianStructureMap (ι := ι) (ν := ν) S) ⁻¹' (U : Set S))
  rw [heq]
  apply isCompact_iUnion
  intro a
  exact ((hU.preimage (Normalized.Chart.Grassmannian.normalizedChart a S).hom).isCompact).image (Gluing.grassmannianChartMap a S).continuous

theorem grassmannianStructureMap_finiteType :
    LocallyOfFiniteType (Gluing.grassmannianStructureMap (ι := ι) (ν := ν) S) ∧
      QuasiCompact (Gluing.grassmannianStructureMap (ι := ι) (ν := ν) S) :=
  ⟨inferInstance, inferInstance⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Grassmannian.FiniteType
