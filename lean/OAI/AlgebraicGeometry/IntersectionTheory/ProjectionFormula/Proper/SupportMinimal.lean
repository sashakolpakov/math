import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports

/-! # Support Minimal -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Proper.SupportMinimal

noncomputable section

/-! At the prescribed codimension in a proper closed intersection,
the generic point has no distinct generalization inside that intersection. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem minimal (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m d : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] (S : Closeds X.carrier)
    (hproper : ∀ D : IrreducibleCloseds X.carrier, (D : Set X.carrier) ⊆ S → d ≤ X.supportCodimension D)
    (C : X.DimensionCycleSupport d) (z : X.carrier) (hz : z ∈ S)
    (hs : z ⤳ CycleClass.Thom.IntersectionGeometry.supportPoint C.val) : z = CycleClass.Thom.IntersectionGeometry.supportPoint C.val := by
  let D : IrreducibleCloseds X.carrier := irreducibleSetEquivPoints.symm z
  have hD : (D : Set X.carrier) ⊆ S :=
    S.isClosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hz)
  have hCD : C.val ≤ D := by
    change (C.val : Set X.carrier) ⊆ (D : Set X.carrier)
    exact (Supports.supportPoint_mem_iff_subset
      ⟨(D : Set X.carrier), D.isClosed⟩ C.val).mp
      (specializes_iff_mem_closure.mp hs)
  have he : C.val = D := by
    by_contra hn
    have hc := Supports.codimension_strictAnti X m (lt_of_le_of_ne hCD hn)
    have hd := hproper D hD
    rw [C.property] at hc
    omega
  have hp : CycleClass.Thom.IntersectionGeometry.supportPoint D = z :=
    (irreducibleSetEquivPoints (α := X.carrier)).apply_symm_apply z
  exact hp.symm.trans (congrArg CycleClass.Thom.IntersectionGeometry.supportPoint he.symm)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Proper.SupportMinimal
