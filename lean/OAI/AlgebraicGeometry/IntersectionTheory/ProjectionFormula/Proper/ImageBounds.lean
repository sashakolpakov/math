import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Proper.IntegralImage
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ClosedDifferenceDimension

/-! # Image Bounds -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Proper.ImageBounds

noncomputable section

/-! Dimension bounds on all supports in a closed set pass to its
actual image under a proper morphism. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) {S : Scheme} (f : S ⟶ X.carrier) [IsProper f]

def image (A : Closeds S) : Closeds X.carrier := ⟨f '' (A : Set S), f.isClosedMap _ A.isClosed⟩

theorem bound (A : Closeds S) (k d : ℕ)
    (hA : ∀ D : IrreducibleCloseds S, (D : Set S) ⊆ A →
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension D (f ≫ X.structureMap) + k ≤ d) :
    ∀ C : IrreducibleCloseds X.carrier, (C : Set X.carrier) ⊆ image X f A →
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension C X.structureMap + k ≤ d := by
  intro C hC
  have hη : CycleClass.Thom.IntersectionGeometry.supportPoint C ∈ image X f A :=
    (Supports.supportPoint_mem_iff_subset (image X f A) C).mpr hC
  obtain ⟨a, ha, hfa⟩ := hη
  let D₀ : IrreducibleCloseds S := irreducibleSetEquivPoints.symm a
  have hD₀ : (D₀ : Set S) ⊆ A := closure_minimal (Set.singleton_subset_iff.mpr ha) A.isClosed
  obtain ⟨b, hb⟩ := Supports.closedComponentSupport_covers S A D₀ hD₀
  let D := CycleClass.Thom.IntersectionGeometry.closedComponentSupport S A b
  have haD : a ∈ D := hb (subset_closure (Set.mem_singleton a))
  let B := CycleClass.Geometric.StratumClosure.integralImageClosure (CycleClass.Geometric.GenericPoint.reducedSupportι D ≫ f)
  have hηB : CycleClass.Thom.IntersectionGeometry.supportPoint C ∈ B := by
    apply subset_closure
    have ha' : a ∈ Set.range (CycleClass.Geometric.GenericPoint.reducedSupportι D) := by rw [CycleClass.Geometric.GenericPoint.range_reducedSupportι]; exact haD
    obtain ⟨z, hz⟩ := ha'
    exact ⟨z, (congrArg f hz).trans hfa⟩
  have hCB : C ≤ B := by
    change (C : Set X.carrier) ⊆ (B : Set X.carrier)
    exact (Supports.supportPoint_mem_iff_subset (⟨(B : Set X.carrier), B.isClosed⟩ : Closeds X.carrier) C).mp hηB
  have hdim := (Foundations.Scheme.SupportDimensionDrop.supportTranscendenceDimension_strictMono X.structureMap).monotone hCB
  have hImage := IntegralImage.dimension_le X (CycleClass.Geometric.GenericPoint.reducedSupportι D ≫ f)
  have hImage' : Foundations.Scheme.SupportDimension.supportTranscendenceDimension B X.structureMap ≤
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension D (f ≫ X.structureMap) := by
    simpa only [B, Foundations.Scheme.SupportDimension.supportTranscendenceDimension, CycleClass.Geometric.SupportFiniteType.supportStructureMap, Category.assoc] using hImage
  have hbound := hA D (Supports.closedComponentSupport_subset S A b)
  omega

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Proper.ImageBounds
