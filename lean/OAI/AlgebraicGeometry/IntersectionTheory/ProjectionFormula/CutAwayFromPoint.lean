import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IndependentLinearCut
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Cut Away From Point -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CutAwayFromPoint

noncomputable section

/-! A hyperplane avoiding one witness in every component except a
designated point raises codimension everywhere away from that point. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.LinearCut

theorem closed_witness (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (x : X.carrier)
    (hx : IsClosed ({x} : Set _)) (W : IrreducibleCloseds X.carrier)
    (hW : ¬ (W : Set X.carrier) ⊆ {x}) :
    ∃ y : X.carrier, y ∈ W ∧ y ≠ x ∧ IsClosed ({y} : Set _) := by
  let : JacobsonSpace X.carrier := LocallyOfFiniteType.jacobsonSpace X.structureMap
  have hn : ((W : Set X.carrier) \ {x}).Nonempty := by
    by_contra h
    exact hW (Set.sdiff_eq_empty.mp (Set.not_nonempty_iff_eq_empty.mp h))
  obtain ⟨y, ⟨hy, hyx⟩, hclosed⟩ := nonempty_inter_closedPoints hn
    (W.isClosed.isLocallyClosed.inter hx.isOpen_compl.isLocallyClosed)
  exact ⟨y, hy, hyx, hclosed⟩

theorem cut (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m k : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] (x : X.carrier)
    (S : Closeds X.carrier)
    (hS : ∀ W : IrreducibleCloseds X.carrier, (W : Set X.carrier) ⊆ S →
      ¬ (W : Set X.carrier) ⊆ {x} → k ≤ X.supportCodimension W)
    (a : Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing X.ambientDimension)
    (ha : ∀ C : irreducibleComponents S,
      ¬ (CycleClass.Thom.IntersectionGeometry.closedComponentSupport X.carrier S C : Set X.carrier) ⊆ {x} →
      ∃ y : X.carrier, y ∈ CycleClass.Thom.IntersectionGeometry.closedComponentSupport X.carrier S C ∧
        a ∉ (X.embedding y).asHomogeneousIdeal) :
    ∀ W : IrreducibleCloseds X.carrier,
      (W : Set X.carrier) ⊆ S ⊓ Projective.LinearCut.zeroSet X.embedding a →
      ¬ (W : Set X.carrier) ⊆ {x} → k + 1 ≤ X.supportCodimension W := by
  intro W hW hWx
  have hWS : (W : Set X.carrier) ⊆ S := fun y hy => (hW hy).1
  obtain ⟨C, hC⟩ := Supports.closedComponentSupport_covers X.carrier S W hWS
  have hCx : ¬ (CycleClass.Thom.IntersectionGeometry.closedComponentSupport X.carrier S C : Set X.carrier) ⊆ {x} :=
    fun h => hWx (hC.trans h)
  obtain ⟨y, hy, hay⟩ := ha C hCx
  have hne : W ≠ CycleClass.Thom.IntersectionGeometry.closedComponentSupport X.carrier S C := by
    intro he
    have hyW : y ∈ W := he ▸ hy
    have hz := (hW hyW).2
    change ¬ a ∉ (X.embedding y).asHomogeneousIdeal at hz
    exact hay (not_not.mp hz)
  have ht := Supports.codimension_strictAnti X m (lt_of_le_of_ne hC hne)
  have hb := hS (CycleClass.Thom.IntersectionGeometry.closedComponentSupport X.carrier S C)
    (Supports.closedComponentSupport_subset X.carrier S C) hCx
  omega

theorem cut_all (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m k : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] (S : Closeds X.carrier)
    (hS : ∀ W : IrreducibleCloseds X.carrier, (W : Set X.carrier) ⊆ S →
      k ≤ X.supportCodimension W)
    (a : Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing X.ambientDimension)
    (ha : ∀ C : irreducibleComponents S,
      a ∉ (X.embedding (CycleClass.Thom.IntersectionGeometry.supportPoint (CycleClass.Thom.IntersectionGeometry.closedComponentSupport X.carrier S C))).asHomogeneousIdeal) :
    ∀ W : IrreducibleCloseds X.carrier,
      (W : Set X.carrier) ⊆ S ⊓ Projective.LinearCut.zeroSet X.embedding a →
      k + 1 ≤ X.supportCodimension W := by
  intro W hW
  have hWS : (W : Set X.carrier) ⊆ S := fun y hy => (hW hy).1
  obtain ⟨C, hC⟩ := Supports.closedComponentSupport_covers X.carrier S W hWS
  have hne : W ≠ CycleClass.Thom.IntersectionGeometry.closedComponentSupport X.carrier S C := by
    intro he
    have hx : CycleClass.Thom.IntersectionGeometry.supportPoint (CycleClass.Thom.IntersectionGeometry.closedComponentSupport X.carrier S C) ∈ (W : Set X.carrier) :=
      he ▸ (W.isIrreducible.isGenericPoint_genericPoint W.isClosed).mem
    have hz := (hW hx).2
    change ¬ a ∉ (X.embedding _).asHomogeneousIdeal at hz
    exact ha C (not_not.mp hz)
  have ht := Supports.codimension_strictAnti X m (lt_of_le_of_ne hC hne)
  have hb := hS (CycleClass.Thom.IntersectionGeometry.closedComponentSupport X.carrier S C)
    (Supports.closedComponentSupport_subset X.carrier S C)
  omega

theorem subset_singleton (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] (S : Closeds X.carrier) (x : X.carrier)
    (hS : ∀ W : IrreducibleCloseds X.carrier, (W : Set X.carrier) ⊆ S →
      ¬ (W : Set X.carrier) ⊆ {x} → m + 1 ≤ X.supportCodimension W) :
    (S : Set X.carrier) ⊆ {x} := by
  intro y hy
  let W : IrreducibleCloseds X.carrier := irreducibleSetEquivPoints.symm y
  have hp : CycleClass.Thom.IntersectionGeometry.supportPoint W = y := irreducibleSetEquivPoints.apply_symm_apply y
  have hW : (W : Set X.carrier) ⊆ S :=
    (Supports.supportPoint_mem_iff_subset S W).mp (hp ▸ hy)
  have hyW : y ∈ W := hp ▸ (W.isIrreducible.isGenericPoint_genericPoint W.isClosed).mem
  by_contra hn
  have hb := hS W hW (fun he => hn (he hyW))
  have hd := Grading.supportDimension_add_codimension X m W
  omega

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CutAwayFromPoint
