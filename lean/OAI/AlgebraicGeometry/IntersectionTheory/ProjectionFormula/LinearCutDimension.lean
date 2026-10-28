import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.FiberCutInduction

/-! # Linear Cut Dimension -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LinearCutDimension

noncomputable section

/-! Linear cuts decrease the function-field dimension of every
remaining component, including on singular support schemes. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.LinearCut

theorem step {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    {n : ℕ} (j : X ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace n) (S : Closeds X) (k d : ℕ)
    (hS : ∀ W : IrreducibleCloseds X, (W : Set X) ⊆ S →
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension W f + k ≤ d)
    (a : Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing n)
    (ha : ∀ C : irreducibleComponents S,
      a ∉ (j (CycleClass.Thom.IntersectionGeometry.supportPoint (CycleClass.Thom.IntersectionGeometry.closedComponentSupport X S C))).asHomogeneousIdeal) :
    ∀ W : IrreducibleCloseds X, (W : Set X) ⊆ S ⊓ Projective.LinearCut.zeroSet j a →
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension W f + (k + 1) ≤ d := by
  intro W hW
  obtain ⟨C, hC⟩ := Supports.closedComponentSupport_covers X S W (fun x hx => (hW hx).1)
  have hne : W ≠ CycleClass.Thom.IntersectionGeometry.closedComponentSupport X S C := by
    intro he
    have hx : CycleClass.Thom.IntersectionGeometry.supportPoint (CycleClass.Thom.IntersectionGeometry.closedComponentSupport X S C) ∈ (W : Set X) :=
      he ▸ (W.isIrreducible.isGenericPoint_genericPoint W.isClosed).mem
    have hz := (hW hx).2
    change ¬ a ∉ (j _).asHomogeneousIdeal at hz
    exact ha C (not_not.mp hz)
  have hd := Foundations.Scheme.SupportDimensionDrop.supportTranscendenceDimension_lt_of_lt W (CycleClass.Thom.IntersectionGeometry.closedComponentSupport X S C) f
    (lt_of_le_of_ne hC hne)
  have hb := hS (CycleClass.Thom.IntersectionGeometry.closedComponentSupport X S C) (Supports.closedComponentSupport_subset X S C)
  omega

theorem cons {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    {n k : ℕ} (j : X ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace n) (L : Fin k → Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing n) (d : ℕ)
    (hL : ∀ W : IrreducibleCloseds X, (W : Set X) ⊆ Projective.LinearCut.commonZero j L →
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension W f + k ≤ d)
    (a : Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing n)
    (ha : ∀ C : irreducibleComponents (Projective.LinearCut.commonZero j L),
      a ∉ (j (CycleClass.Thom.IntersectionGeometry.supportPoint (CycleClass.Thom.IntersectionGeometry.closedComponentSupport X (Projective.LinearCut.commonZero j L) C))).asHomogeneousIdeal) :
    ∀ W : IrreducibleCloseds X, (W : Set X) ⊆ Projective.LinearCut.commonZero j (Fin.cons a L) →
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension W f + (k + 1) ≤ d := by
  rw [FiberCutInduction.commonZero_cons]
  exact step f j (Projective.LinearCut.commonZero j L) k d hL a ha

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LinearCutDimension
