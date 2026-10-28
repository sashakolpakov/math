import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProductSupportDimension
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.SupportDimension

/-! # Product Support -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.ProductSupport

noncomputable section

section

/-! Product-support dimension bounds respect closed supports in
both factors, without requiring the ambient factors to be integral. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {K : Type} [Field K] {X Y : Scheme}
  (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
  (C : IrreducibleCloseds X) (D : IrreducibleCloseds Y)

def inclusion : pullback (CycleClass.Geometric.GenericPoint.reducedSupportι C ≫ f) (CycleClass.Geometric.GenericPoint.reducedSupportι D ≫ g) ⟶ pullback f g :=
  pullback.map _ _ f g (CycleClass.Geometric.GenericPoint.reducedSupportι C) (CycleClass.Geometric.GenericPoint.reducedSupportι D) (𝟙 _)
    (Category.comp_id _) (Category.comp_id _)

instance closed : IsClosedImmersion (inclusion f g C D) :=
  MorphismProperty.pullbackMap (P := @IsClosedImmersion) inferInstance inferInstance rfl rfl

theorem range : Set.range (inclusion f g C D) =
    pullback.fst f g ⁻¹' (C : Set X) ∩ pullback.snd f g ⁻¹' (D : Set Y) := by
  rw [inclusion, Scheme.Pullback.range_map]
  exact congrArg₂ (fun S : Set X => fun T : Set Y =>
    pullback.fst f g ⁻¹' S ∩ pullback.snd f g ⁻¹' T) (CycleClass.Geometric.GenericPoint.range_reducedSupportι C) (CycleClass.Geometric.GenericPoint.range_reducedSupportι D)

theorem over_base : inclusion f g C D ≫ pullback.fst f g ≫ f =
    pullback.fst (CycleClass.Geometric.GenericPoint.reducedSupportι C ≫ f) (CycleClass.Geometric.GenericPoint.reducedSupportι D ≫ g) ≫ CycleClass.Geometric.GenericPoint.reducedSupportι C ≫ f := by
  rw [inclusion, pullback.lift_fst_assoc, Category.assoc]

theorem bound [LocallyOfFiniteType f] [LocallyOfFiniteType g]
    (W : IrreducibleCloseds ↥(pullback f g))
    (hW : (W : Set ↥(pullback f g)) ⊆
      pullback.fst f g ⁻¹' (C : Set X) ∩ pullback.snd f g ⁻¹' (D : Set Y)) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension W (pullback.fst f g ≫ f) ≤
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension C f + Foundations.Scheme.SupportDimension.supportTranscendenceDimension D g := by
  have hr : (W : Set ↥(pullback f g)) ⊆ Set.range (inclusion f g C D) := by rwa [ProductSupport.range]
  let E := SupportDimension.preimage (inclusion f g C D) W hr
  have hd := SupportDimension.dimension (inclusion f g C D) W hr (pullback.fst f g ≫ f)
  rw [← hd, over_base]
  exact ProductSupportDimension.bound (CycleClass.Geometric.GenericPoint.reducedSupportι C ≫ f) (CycleClass.Geometric.GenericPoint.reducedSupportι D ≫ g) E

end

/-! Dimension bounds on two closed factor subsets add on their
inverse-image intersection in the actual product scheme. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace Bounds

theorem imageClosure_coe {X Y : Scheme} (f : X ⟶ Y) (W : IrreducibleCloseds X) :
    (CycleClass.Geometric.StratumClosure.integralImageClosure (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ f) : Set Y) = closure (f '' (W : Set X)) := by
  rw [CycleClass.Geometric.StratumClosure.integralImageClosure_coe]
  change closure (Set.range (f ∘ CycleClass.Geometric.GenericPoint.reducedSupportι W)) = _
  rw [Set.range_comp, CycleClass.Geometric.GenericPoint.range_reducedSupportι]

theorem bound {K : Type} [Field K] {X Y : Scheme}
    (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
    [LocallyOfFiniteType f] [LocallyOfFiniteType g]
    (A : Closeds X) (B : Closeds Y) (a b r s : ℕ)
    (hA : ∀ C : IrreducibleCloseds X, (C : Set X) ⊆ A → Foundations.Scheme.SupportDimension.supportTranscendenceDimension C f + a ≤ r)
    (hB : ∀ D : IrreducibleCloseds Y, (D : Set Y) ⊆ B → Foundations.Scheme.SupportDimension.supportTranscendenceDimension D g + b ≤ s)
    (W : IrreducibleCloseds ↥(pullback f g))
    (hW : (W : Set ↥(pullback f g)) ⊆
      pullback.fst f g ⁻¹' (A : Set X) ∩ pullback.snd f g ⁻¹' (B : Set Y)) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension W (pullback.fst f g ≫ f) + (a + b) ≤ r + s := by
  let C := CycleClass.Geometric.StratumClosure.integralImageClosure (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ pullback.fst f g)
  let D := CycleClass.Geometric.StratumClosure.integralImageClosure (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ pullback.snd f g)
  have hC : (C : Set X) ⊆ A := by
    rw [imageClosure_coe]
    apply closure_minimal _ A.isClosed
    rintro _ ⟨x, hx, rfl⟩
    exact (hW hx).1
  have hD : (D : Set Y) ⊆ B := by
    rw [imageClosure_coe]
    apply closure_minimal _ B.isClosed
    rintro _ ⟨x, hx, rfl⟩
    exact (hW hx).2
  have hCD : (W : Set ↥(pullback f g)) ⊆
      pullback.fst f g ⁻¹' (C : Set X) ∩ pullback.snd f g ⁻¹' (D : Set Y) := by
    intro x hx
    constructor
    · change pullback.fst f g x ∈ (C : Set X)
      rw [imageClosure_coe]
      exact subset_closure ⟨x, hx, rfl⟩
    · change pullback.snd f g x ∈ (D : Set Y)
      rw [imageClosure_coe]
      exact subset_closure ⟨x, hx, rfl⟩
  have hd := ProductSupport.bound f g C D W hCD
  have ha := hA C hC
  have hb := hB D hD
  omega

end Bounds

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.ProductSupport
