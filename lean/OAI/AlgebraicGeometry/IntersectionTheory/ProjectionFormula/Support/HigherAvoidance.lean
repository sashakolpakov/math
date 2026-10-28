import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.ChowMoving
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.ClosedComponents

/-! # Higher Avoidance -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.HigherAvoidance

noncomputable section

section

/-! Proper moving against higher-codimension auxiliary supports
removes them from every coefficient in the requested intersection degree.
The vanishing follows from disjoint native supports at that point. -/

open _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem point_notMem (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p q : ℕ)
    (A : X.DimensionCycleSupport p) (B : IrreducibleCloseds X.carrier)
    (hB : q < X.supportCodimension B)
    (hp : ∀ D : IrreducibleCloseds X.carrier,
      (D : Set X.carrier) ⊆ (A.val : Set X.carrier) ∩ (B : Set X.carrier) →
        p + X.supportCodimension B ≤ X.supportCodimension D)
    (C : X.DimensionCycleSupport (p + q)) :
    CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∉ (A.val : Set X.carrier) ∩ (B : Set X.carrier) := by
  intro hx
  let S : Closeds X.carrier := ⟨(A.val : Set X.carrier) ∩ (B : Set X.carrier), A.val.isClosed.inter B.isClosed⟩
  have hc := hp C.val ((Supports.supportPoint_mem_iff_subset S C.val).mp hx)
  rw [C.property] at hc
  omega

theorem coefficient_zero (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p q : ℕ)
    (A : X.DimensionCycleSupport p) (B : IrreducibleCloseds X.carrier)
    (hB : q < X.supportCodimension B)
    (hp : ∀ D : IrreducibleCloseds X.carrier,
      (D : Set X.carrier) ⊆ (A.val : Set X.carrier) ∩ (B : Set X.carrier) →
        p + X.supportCodimension B ≤ X.supportCodimension D)
    (C : X.DimensionCycleSupport (p + q)) :
    CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X A.val B C.val = 0 :=
  dite_eq_right (point_notMem X p q A B hB hp C)

theorem move (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] {τ : Type} [Finite τ]
    (Z : τ → IrreducibleCloseds X.carrier) (hZ : ∀ t, q < X.supportCodimension (Z t))
    (a : X.RationalDimensionCycle p) :
    ∃ a' : X.RationalDimensionCycle p, CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X p a a' ∧
      ∀ t, ∀ A ∈ a'.support, ∀ C : X.DimensionCycleSupport (p + q),
        CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X A.val (Z t) C.val = 0 := by
  obtain ⟨a', ha', hproper⟩ := General.ChowMoving.cycle X m Z p a
  exact ⟨a', ha', fun t A hA C => coefficient_zero X p q A (Z t) (hZ t) (hproper t A hA) C⟩

end

/-! A finite collection of proper closed strata ensures that a
support rational function is a unit at every generic point of an
expected-dimensional intersection, in arbitrary codimension. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

namespace UnitStrata

theorem exists_data (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m k : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (W : X.DimensionCycleSupport k) (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).functionField) (hg : g ≠ 0) :
    ∃ F : Finset (IrreducibleCloseds X.carrier),
      (∀ B ∈ F, k < X.supportCodimension B) ∧
      ∀ (p : ℕ) (A : X.DimensionCycleSupport p),
        (∀ B ∈ F, ∀ D : IrreducibleCloseds X.carrier,
          (D : Set X.carrier) ⊆ (A.val : Set X.carrier) ∩ (B : Set X.carrier) →
            p + X.supportCodimension B ≤ X.supportCodimension D) →
        ∀ C : X.DimensionCycleSupport (p + k), C.val ≤ A.val → C.val ≤ W.val →
          ∀ hxW : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (W.val : Set X.carrier),
          ∃ u : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPreimage W.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxW),
            IsUnit u ∧ algebraMap _ (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).functionField u = g := by
  let Y := CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val
  let i := CycleClass.Geometric.GenericPoint.reducedSupportι W.val
  obtain ⟨U, _, a, hU, hga, ha⟩ := exists_isUnit_germ_eq Y g hg
  let : Nonempty U := hU
  have hηU : genericPoint Y ∈ U :=
    ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr (by simpa using hU)
  let S : Closeds X.carrier := ⟨i '' (U : Set Y)ᶜ,
    i.isClosedEmbedding.isClosedMap _ U.isOpen.isClosed_compl⟩
  have hSW : (S : Set X.carrier) ⊆ (W.val : Set X.carrier) := by
    rintro x ⟨y, _, rfl⟩
    rw [← CycleClass.Geometric.GenericPoint.range_reducedSupportι]
    exact ⟨y, rfl⟩
  have hηS : CycleClass.Thom.IntersectionGeometry.supportPoint W.val ∉ S := by
    rintro ⟨y, hy, he⟩
    have hyη : y = genericPoint Y := i.isEmbedding.injective
      (he.trans (CycleClass.Geometric.GenericPoint.reducedSupport_genericPoint_eq W.val).symm)
    exact hy (hyη ▸ hηU)
  let F := ProjectionFormula.Finite.ClosedComponents.components X.carrier S
  have hdim (B : IrreducibleCloseds X.carrier) (hB : B ∈ F) : k < X.supportCodimension B := by
    have hBS := ProjectionFormula.Finite.ClosedComponents.subset X.carrier S B hB
    have hBW : B < W.val := lt_of_le_of_ne (hBS.trans hSW) (by
      intro he
      exact hηS (hBS (he.symm ▸
        (W.val.isIrreducible.isGenericPoint_genericPoint W.val.isClosed).mem)))
    have h := Supports.codimension_strictAnti X m hBW
    rwa [W.property] at h
  refine ⟨F, hdim, ?_⟩
  intro p A hA C hCA _ hxW
  let y := CycleClass.Thom.IntersectionGeometry.supportPreimage W.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxW
  have hyU : y ∈ U := by
    by_contra hnot
    have hxS : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ S :=
      ⟨y, hnot, CycleClass.Thom.IntersectionGeometry.supportPreimage_spec W.val _ hxW⟩
    have hCS := (Supports.supportPoint_mem_iff_subset S C.val).mp hxS
    obtain ⟨D, hCD⟩ := Supports.closedComponentSupport_covers X.carrier S C.val hCS
    let B := CycleClass.Thom.IntersectionGeometry.closedComponentSupport X.carrier S D
    have hB : B ∈ F := (ProjectionFormula.Finite.ClosedComponents.mem_iff X.carrier S B).mpr ⟨D, rfl⟩
    have hbound := hA B hB C.val (fun x hx => ⟨hCA hx, hCD hx⟩)
    have hbad := hdim B hB
    rw [C.property] at hbound
    omega
  exact ⟨Y.presheaf.germ U y hyU a, ha.map (Y.presheaf.germ U y hyU).hom,
    (Y.algebraMap_germ_eq_germToFunctionField hyU a).trans hga⟩

end UnitStrata

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.HigherAvoidance
