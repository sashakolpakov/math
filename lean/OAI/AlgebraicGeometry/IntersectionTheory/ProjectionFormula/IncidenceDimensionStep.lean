import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports
import OAI.AlgebraicGeometry.Foundations.Scheme.SupportDimensionDrop

/-! # Incidence Dimension Step -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IncidenceDimensionStep

noncomputable section

/-! A dimension step for coincidence loci: old components must be
cut properly, while a separately bounded base locus may persist. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports

theorem step {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (S R B F : Closeds X) (k d : ℕ)
    (hRS : (R : Set X) ⊆ S ⊔ B)
    (hS : ∀ W : IrreducibleCloseds X, (W : Set X) ⊆ S → ¬ (W : Set X) ⊆ F →
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension W f + k ≤ d)
    (hB : ∀ W : IrreducibleCloseds X, (W : Set X) ⊆ B → ¬ (W : Set X) ⊆ F →
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension W f + (k + 1) ≤ d)
    (hcut : ∀ C : irreducibleComponents S,
      ¬ (CycleClass.Thom.IntersectionGeometry.closedComponentSupport X S C : Set X) ⊆ F →
      ¬ (CycleClass.Thom.IntersectionGeometry.closedComponentSupport X S C : Set X) ⊆ B →
      ∃ x ∈ CycleClass.Thom.IntersectionGeometry.closedComponentSupport X S C, x ∉ R) :
    ∀ W : IrreducibleCloseds X, (W : Set X) ⊆ R → ¬ (W : Set X) ⊆ F →
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension W f + (k + 1) ≤ d := by
  intro W hW hWF
  have hu : (W : Set X) ⊆ (S : Set X) ∪ B := hW.trans hRS
  rcases isPreirreducible_iff_isClosed_union_isClosed.mp W.isIrreducible.isPreirreducible
      S B S.isClosed B.isClosed hu with hWS | hWB
  · obtain ⟨C, hC⟩ := Supports.closedComponentSupport_covers X S W hWS
    have hCF : ¬ (CycleClass.Thom.IntersectionGeometry.closedComponentSupport X S C : Set X) ⊆ F := fun h => hWF (hC.trans h)
    by_cases hCB : (CycleClass.Thom.IntersectionGeometry.closedComponentSupport X S C : Set X) ⊆ B
    · exact hB W (hC.trans hCB) hWF
    obtain ⟨x, hxC, hxR⟩ := hcut C hCF hCB
    have hne : W ≠ CycleClass.Thom.IntersectionGeometry.closedComponentSupport X S C := by
      intro he
      exact hxR (hW (he ▸ hxC))
    have hd := Foundations.Scheme.SupportDimensionDrop.supportTranscendenceDimension_lt_of_lt W (CycleClass.Thom.IntersectionGeometry.closedComponentSupport X S C) f
      (lt_of_le_of_ne hC hne)
    have hb := hS (CycleClass.Thom.IntersectionGeometry.closedComponentSupport X S C) (Supports.closedComponentSupport_subset X S C) hCF
    omega
  · exact hB W hWB hWF

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IncidenceDimensionStep
