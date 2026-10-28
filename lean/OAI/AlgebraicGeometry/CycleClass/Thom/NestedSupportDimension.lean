import OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.SmoothLocus
import OAI.AlgebraicGeometry.Foundations.Scheme.SupportDimensionDrop

/-! # Nested Support Dimension -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.NestedSupportDimension.Constructions

noncomputable section

/-! Two intrinsic specialization steps inside a reduced closed support
give two actual support-dimension drops in the ambient scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace _root_.Order

theorem closedImmersion_strictMono {A B : Scheme} (i : A ⟶ B) [IsClosedImmersion i] :
    StrictMono i := by
  intro x y h
  apply lt_of_le_not_ge
  · exact Scheme.le_iff_specializes.mpr
      ((Scheme.le_iff_specializes.mp h.le).map i.continuous)
  · intro he
    apply not_le_of_gt h
    apply Scheme.le_iff_specializes.mpr
    exact i.isClosedEmbedding.isEmbedding.isInducing.specializes_iff.mp
      (Scheme.le_iff_specializes.mp he)

theorem supportPoint_dimension_add_two_le {X : Scheme}
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (W : IrreducibleCloseds X) (x : Geometric.GenericPoint.reducedSupportScheme W) (hx : 1 < coheight x) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension
      (irreducibleSetEquivPoints.symm (Geometric.GenericPoint.reducedSupportι W x)) f + 2 ≤
        Foundations.Scheme.SupportDimension.supportTranscendenceDimension W f := by
  obtain ⟨y, z, hyz, hxy⟩ :=
    (Order.one_lt_height_iff (α := (Geometric.GenericPoint.reducedSupportScheme W)ᵒᵈ)).mp hx
  let i := Geometric.GenericPoint.reducedSupportι W
  let C : Geometric.GenericPoint.reducedSupportScheme W → IrreducibleCloseds X :=
    fun t => irreducibleSetEquivPoints.symm (i t)
  have h₁ : C x < C y := irreducibleSetEquivPoints.symm.strictMono
    (closedImmersion_strictMono i hxy)
  have h₂ : C y < C z := irreducibleSetEquivPoints.symm.strictMono
    (closedImmersion_strictMono i hyz)
  have h₃ : C z ≤ W := by
    change closure {i z} ⊆ (W : Set X)
    apply closure_minimal _ W.isClosed
    rintro t rfl
    rw [← Geometric.GenericPoint.range_reducedSupportι W]
    exact ⟨z, rfl⟩
  have hd₁ := Foundations.Scheme.SupportDimensionDrop.supportTranscendenceDimension_lt_of_lt (C x) (C y) f h₁
  have hd₂ := Foundations.Scheme.SupportDimensionDrop.supportTranscendenceDimension_lt_of_lt (C y) (C z) f h₂
  have hd₃ := (Foundations.Scheme.SupportDimensionDrop.supportTranscendenceDimension_strictMono f).monotone h₃
  change Foundations.Scheme.SupportDimension.supportTranscendenceDimension (C x) f + 2 ≤
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension W f
  omega

end

end OAI.AlgebraicGeometry.CycleClass.Thom.NestedSupportDimension.Constructions
