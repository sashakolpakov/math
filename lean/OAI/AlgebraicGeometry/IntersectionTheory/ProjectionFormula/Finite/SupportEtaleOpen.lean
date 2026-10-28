import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Generic.EtaleMorphism
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Proper.EtaleRestriction
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.ClosedComponents
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Fields

/-! # Support Etale Open -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.SupportEtaleOpen

noncomputable section

/-! A dimension-preserving support map is finite etale away from
a finite family of target supports of strictly larger codimension. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Map

theorem exists_data {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver)
    (n : ℕ) [SmoothOfRelativeDimension n Y.structureMap] (W : IrreducibleCloseds X.carrier)
    (hd : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (ProperCycleLinearity.imageSupport f W) Y.structureMap =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension W X.structureMap) :
    ∃ U : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).Opens,
      genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) ∈ U ∧ Etale (U.ι ≫ Support.Map.supportImageMap f W) ∧
      ∃ F : Finset (IrreducibleCloseds Y.carrier),
        (∀ D ∈ F, Y.supportCodimension (ProperCycleLinearity.imageSupport f W) < Y.supportCodimension D) ∧
        ∀ x : CycleClass.Geometric.GenericPoint.reducedSupportScheme W, x ∉ U →
          ∃ D ∈ F, f.left (CycleClass.Geometric.GenericPoint.reducedSupportι W x) ∈ (D : Set Y.carrier) := by
  let u := Support.Map.supportImageMap f W
  obtain ⟨U, hη, hU⟩ := Generic.EtaleMorphism.exists_open u
    (CycleClass.Geometric.SupportFiniteType.supportStructureMap (ProperCycleLinearity.imageSupport f W) Y.structureMap) (Support.Map.supportImageMap_genericPoint f W) (by
      rw [Support.Map.supportImageMap_over]
      exact hd)
  let S : Closeds X.carrier := ⟨(CycleClass.Geometric.GenericPoint.reducedSupportι W) '' (U : Set (CycleClass.Geometric.GenericPoint.reducedSupportScheme W))ᶜ,
    (CycleClass.Geometric.GenericPoint.reducedSupportι W).isClosedMap _ U.isOpen.isClosed_compl⟩
  let K := ClosedComponents.components X.carrier S
  have hSW : (S : Set X.carrier) ⊆ W := by
    rintro x ⟨z, _, rfl⟩
    rw [← CycleClass.Geometric.GenericPoint.range_reducedSupportι W]
    exact Set.mem_range_self z
  have hηS : CycleClass.Thom.IntersectionGeometry.supportPoint W ∉ (S : Set X.carrier) := by
    rintro ⟨z, hz, he⟩
    have hzη : z = genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) :=
      (CycleClass.Geometric.GenericPoint.reducedSupportι W).isEmbedding.injective (he.trans (CycleClass.Geometric.GenericPoint.reducedSupport_genericPoint_eq W).symm)
    exact hz (hzη.symm ▸ hη)
  have hKW (Z : IrreducibleCloseds X.carrier) (hZ : Z ∈ K) : Z < W := by
    have hZS := ClosedComponents.subset X.carrier S Z hZ
    apply lt_of_le_of_ne (hZS.trans hSW)
    intro he
    exact hηS (hZS (he.symm ▸ (W.isIrreducible.isGenericPoint_genericPoint W.isClosed).mem))
  refine ⟨U, hη, hU, K.image (ProperCycleLinearity.imageSupport f), ?_, ?_⟩
  · intro D hD
    obtain ⟨Z, hZ, rfl⟩ := Finset.mem_image.mp hD
    have hdim := (Support.Fields.image_dimension_le f Z).trans_lt
      (Foundations.Scheme.SupportDimensionDrop.supportTranscendenceDimension_strictMono X.structureMap (hKW Z hZ))
    change Foundations.Scheme.SupportDimension.supportTranscendenceDimension (ProperCycleLinearity.imageSupport f Z) Y.structureMap <
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension W X.structureMap at hdim
    rw [← hd] at hdim
    have hW := Grading.supportDimension_add_codimension Y n (ProperCycleLinearity.imageSupport f W)
    have hZ := Grading.supportDimension_add_codimension Y n (ProperCycleLinearity.imageSupport f Z)
    omega
  · intro x hx
    let z := CycleClass.Geometric.GenericPoint.reducedSupportι W x
    let C := irreducibleSetEquivPoints.symm z
    have hz : z ∈ (S : Set X.carrier) := ⟨x, hx, rfl⟩
    have hC : (C : Set X.carrier) ⊆ S :=
      (Supports.supportPoint_mem_iff_subset S C).mp (by
        have hp : CycleClass.Thom.IntersectionGeometry.supportPoint C = z := irreducibleSetEquivPoints.apply_symm_apply z
        rw [hp]
        exact hz)
    obtain ⟨D, hCD⟩ := Supports.closedComponentSupport_covers X.carrier S C hC
    let Z := CycleClass.Thom.IntersectionGeometry.closedComponentSupport X.carrier S D
    have hZ : Z ∈ K := (ClosedComponents.mem_iff X.carrier S Z).mpr ⟨D, rfl⟩
    refine ⟨ProperCycleLinearity.imageSupport f Z, Finset.mem_image.mpr ⟨Z, hZ, rfl⟩, ?_⟩
    rw [ProperCycleLinearity.imageSupport_eq_image]
    refine ⟨z, hCD ?_, rfl⟩
    exact subset_closure (Set.mem_singleton z)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.SupportEtaleOpen
