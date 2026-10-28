import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Flat.SupportDimension
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.ClosedComponents
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.ChowMoving

/-! # Proper Moving -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.ProperMoving

noncomputable section

/-! A finite family of target supports controls proper inverse-image
position for any source support. Induction on source dimension treats
the complement of the actual smooth locus, so no flatness of the
original morphism is assumed. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Map

def ProperAgainst (Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ) (A : Y.DimensionCycleSupport p)
    (F : Finset (IrreducibleCloseds Y.carrier)) : Prop :=
  ∀ Z ∈ F, ∀ C : IrreducibleCloseds Y.carrier,
    (C : Set Y.carrier) ⊆ (A.val : Set Y.carrier) ∩ Z → p + Y.supportCodimension Z ≤ Y.supportCodimension C

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver)
  (m n : ℕ) [SmoothOfRelativeDimension m X.structureMap] [SmoothOfRelativeDimension n Y.structureMap]

include m n in
theorem family (W : IrreducibleCloseds X.carrier) :
    ∃ F : Finset (IrreducibleCloseds Y.carrier), ProperCycleLinearity.imageSupport f W ∈ F ∧
      ∀ (p : ℕ) (A : Y.DimensionCycleSupport p), ProperAgainst Y p A F →
        ∀ C : IrreducibleCloseds X.carrier,
          (C : Set X.carrier) ⊆ (W : Set X.carrier) ∩ f.left ⁻¹' (A.val : Set Y.carrier) →
            X.supportCodimension W + p ≤ X.supportCodimension C := by
  refine (measure (fun W : IrreducibleCloseds X.carrier => Foundations.Scheme.SupportDimension.supportTranscendenceDimension W X.structureMap)).wf.induction
    (C := fun W => ∃ F : Finset (IrreducibleCloseds Y.carrier), ProperCycleLinearity.imageSupport f W ∈ F ∧
      ∀ (p : ℕ) (A : Y.DimensionCycleSupport p), ProperAgainst Y p A F →
        ∀ C : IrreducibleCloseds X.carrier,
          (C : Set X.carrier) ⊆ (W : Set X.carrier) ∩ f.left ⁻¹' (A.val : Set Y.carrier) →
            X.supportCodimension W + p ≤ X.supportCodimension C) W ?_
  intro W ih
  let u := Support.Map.supportImageMap f W
  let U := u.smoothLocus
  have hη : genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) ∈ U :=
    Generic.SmoothMorphism.generic_mem u (CycleClass.Geometric.SupportFiniteType.supportStructureMap (ProperCycleLinearity.imageSupport f W) Y.structureMap)
      (Support.Map.supportImageMap_genericPoint f W)
  let S : Closeds X.carrier := ⟨(CycleClass.Geometric.GenericPoint.reducedSupportι W) '' (U : Set (CycleClass.Geometric.GenericPoint.reducedSupportScheme W))ᶜ,
    (CycleClass.Geometric.GenericPoint.reducedSupportι W).isClosedMap _ U.isOpen.isClosed_compl⟩
  have hSW : (S : Set X.carrier) ⊆ W := by
    rintro x ⟨y, _, rfl⟩
    rw [← CycleClass.Geometric.GenericPoint.range_reducedSupportι W]
    exact Set.mem_range_self y
  have hηS : CycleClass.Thom.IntersectionGeometry.supportPoint W ∉ (S : Set X.carrier) := by
    rintro ⟨y, hy, he⟩
    have hyη : y = genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) :=
      (CycleClass.Geometric.GenericPoint.reducedSupportι W).isEmbedding.injective (he.trans (CycleClass.Geometric.GenericPoint.reducedSupport_genericPoint_eq W).symm)
    exact hy (hyη.symm ▸ hη)
  let K := Finite.ClosedComponents.components X.carrier S
  have hKW (Z : K) : Z.val < W := by
    have hZS := Finite.ClosedComponents.subset X.carrier S Z.val Z.property
    apply lt_of_le_of_ne (hZS.trans hSW)
    intro he
    exact hηS (hZS (he.symm ▸ (W.isIrreducible.isGenericPoint_genericPoint W.isClosed).mem))
  have hrec (Z : K) := ih Z.val (Foundations.Scheme.SupportDimensionDrop.supportTranscendenceDimension_strictMono X.structureMap (hKW Z))
  choose F hmem hproper using hrec
  let T := insert (ProperCycleLinearity.imageSupport f W) (Finset.univ.biUnion F)
  refine ⟨T, Finset.mem_insert_self _ _, ?_⟩
  intro p A hA C hC
  have hCW : C ≤ W := fun x hx => (hC hx).1
  let x := CycleClass.Thom.IntersectionGeometry.supportPreimage W (CycleClass.Thom.IntersectionGeometry.supportPoint C) (hCW (C.isIrreducible.isGenericPoint_genericPoint C.isClosed).mem)
  by_cases hx : x ∈ U
  · have hd := Flat.SupportDimension.at_smooth f m n W C hCW hx
    have hCI : (ProperCycleLinearity.imageSupport f C : Set Y.carrier) ⊆ (A.val : Set Y.carrier) ∩ ProperCycleLinearity.imageSupport f W := by
      rw [ProperCycleLinearity.imageSupport_eq_image, ProperCycleLinearity.imageSupport_eq_image]
      rintro _ ⟨z, hz, rfl⟩
      exact ⟨(hC hz).2, ⟨z, (hC hz).1, rfl⟩⟩
    have ha := hA (ProperCycleLinearity.imageSupport f W) (Finset.mem_insert_self _ _) (ProperCycleLinearity.imageSupport f C) hCI
    omega
  · have hxS : CycleClass.Thom.IntersectionGeometry.supportPoint C ∈ (S : Set X.carrier) := ⟨x, hx, CycleClass.Thom.IntersectionGeometry.supportPreimage_spec W _ _⟩
    have hCS := (Supports.supportPoint_mem_iff_subset S C).mp hxS
    obtain ⟨Z, hCZ⟩ := Supports.closedComponentSupport_covers X.carrier S C hCS
    let V := CycleClass.Thom.IntersectionGeometry.closedComponentSupport X.carrier S Z
    have hV : V ∈ K := (Finite.ClosedComponents.mem_iff X.carrier S V).mpr ⟨Z, rfl⟩
    have hp : ProperAgainst Y p A (F ⟨V, hV⟩) := by
      intro B hB D hD
      exact hA B (Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨⟨V, hV⟩, Finset.mem_univ _, hB⟩)) D hD
    have hv := hproper ⟨V, hV⟩ p A hp C (fun z hz => ⟨hCZ hz, (hC hz).2⟩)
    have hw := (Supports.codimension_strictAnti X m).antitone (hKW ⟨V, hV⟩).le
    omega

include m n in
theorem cycle (p q : ℕ) (a : Y.RationalDimensionCycle p) (b : X.RationalDimensionCycle q) :
    ∃ a' : Y.RationalDimensionCycle p, CycleClass.Thom.IntersectionGeometry.RationallyEquivalent Y p a a' ∧
      ∀ A ∈ a'.support, ∀ B ∈ b.support, ∀ C : IrreducibleCloseds X.carrier,
        (C : Set X.carrier) ⊆ (B.val : Set X.carrier) ∩ f.left ⁻¹' (A.val : Set Y.carrier) →
          p + q ≤ X.supportCodimension C := by
  choose F hmem hproper using (fun B : b.support => family f m n B.val.val)
  let T := Finset.univ.biUnion F
  obtain ⟨a', ha, hp⟩ := General.ChowMoving.cycle Y n (fun Z : T => Z.val) p a
  refine ⟨a', ha, ?_⟩
  intro A hA B hB C hC
  have hP : ProperAgainst Y p A (F ⟨B, hB⟩) := by
    intro Z hZ D hD
    exact hp ⟨Z, Finset.mem_biUnion.mpr ⟨⟨B, hB⟩, Finset.mem_univ _, hZ⟩⟩ A hA D hD
  have he := hproper ⟨B, hB⟩ p A hP C hC
  rw [B.property] at he
  omega

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.ProperMoving
