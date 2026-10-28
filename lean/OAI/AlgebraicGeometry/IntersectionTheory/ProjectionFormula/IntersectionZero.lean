import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Open.Support
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports

/-! # Intersection Zero -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IntersectionZero

noncomputable section

/-! Exact local intersection coefficients when the first support has
codimension zero. Such a support is an open component, so its local module
is free of rank one and its intersection just selects that component. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical BigOperators

theorem eq_of_subset_of_codimension_eq (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] {A B : IrreducibleCloseds X.carrier}
    (h : A ≤ B) (he : X.supportCodimension A = X.supportCodimension B) : A = B := by
  by_contra hne
  have ht := Supports.codimension_strictAnti X m (lt_of_le_of_ne h hne)
  omega

theorem meetProperly_zero_left (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (a : X.RationalDimensionCycle 0) (b : X.RationalDimensionCycle q) :
    CycleClass.Thom.IntersectionGeometry.MeetProperly X 0 q a b := by
  intro A _ B _ C hC
  have hCB : C ≤ B.val := fun x hx => (hC hx).2
  have h := (Supports.codimension_strictAnti X m).antitone hCB
  simpa only [B.property, zero_add] using h

theorem subset_of_mem_zero_support (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] (A : X.DimensionCycleSupport 0)
    (W : IrreducibleCloseds X.carrier) (x : X.carrier)
    (hxW : x ∈ (W : Set X.carrier)) (hxA : x ∈ (A.val : Set X.carrier)) : W ≤ A.val := by
  apply (Supports.supportPoint_mem_iff_subset
    ⟨A.val, A.val.isClosed⟩ W).mp
  exact ((W.isIrreducible.isGenericPoint_genericPoint W.isClosed).mem_open_set_iff
    (Open.Support.codimension_zero_isOpen X m A)).mpr ⟨x, hxW, hxA⟩

theorem multiplicity_zero_left (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] (A : X.DimensionCycleSupport 0)
    (B C : X.DimensionCycleSupport q) :
    CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X A.val B.val C.val =
      if B = C ∧ C.val ≤ A.val then 1 else 0 := by
  by_cases h : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (A.val : Set X.carrier) ∩ (B.val : Set X.carrier)
  · have hCA := (Supports.supportPoint_mem_iff_subset
      ⟨A.val, A.val.isClosed⟩ C.val).mp h.1
    have hCB := (Supports.supportPoint_mem_iff_subset
      ⟨B.val, B.val.isClosed⟩ C.val).mp h.2
    have he : B = C := Subtype.ext (eq_of_subset_of_codimension_eq X m hCB
      (C.property.trans B.property.symm)).symm
    subst B
    rw [ite_eq_left ⟨rfl, hCA⟩, CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity, dite_eq_left h]
    let : IsOpenImmersion (CycleClass.Geometric.GenericPoint.reducedSupportι A.val) := Open.Support.inclusion_isOpenImmersion
      A.val (Open.Support.codimension_zero_isOpen X m A)
    change (∑ i ∈ Finset.range (X.ambientDimension + 1), (-1 : ℚ) ^ i *
      (Module.length (X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val))
        (((Tor (ModuleCat (X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val))) i).obj
          (CycleClass.Thom.IntersectionGeometry.localSupportModule X.carrier A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) h.1)).obj
            (CycleClass.Thom.IntersectionGeometry.localSupportModule X.carrier C.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) h.2))).toNat) = 1
    rw [ProjectionFormula.Tor.Flat.euler_length_of_unit _ _ _
      (Open.Support.localModuleEquiv A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) h.1)]
    simp [Open.Support.localModule_length_at_generic]
  · rw [CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity, dite_eq_right h, ite_eq_right]
    rintro ⟨rfl, hCA⟩
    have hc : CycleClass.Thom.IntersectionGeometry.supportPoint B.val ∈ (B.val : Set X.carrier) :=
      (B.val.isIrreducible.isGenericPoint_genericPoint B.val.isClosed).mem
    exact h ⟨hCA hc, hc⟩

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IntersectionZero
