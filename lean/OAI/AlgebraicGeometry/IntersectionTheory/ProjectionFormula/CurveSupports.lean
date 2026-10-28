import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ZeroComponents

/-! # Curve Supports -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CurveSupports

noncomputable section

/-! The actual supports of positive-codimension cycles on a smooth curve
are closed points. Codimension-one supports have native scheme coheight one. -/

open _root_.AlgebraicGeometry _root_.TopologicalSpace _root_.Order

theorem codimension_le (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] (A : IrreducibleCloseds X.carrier) :
    X.supportCodimension A ≤ m := by
  have h := Grading.supportDimension_add_codimension X m A
  omega

theorem coheight_le_codimension (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] (A : IrreducibleCloseds X.carrier) :
    coheight (CycleClass.Thom.IntersectionGeometry.supportPoint A) ≤ X.supportCodimension A := by
  have h := coheight_le_coheight_apply_of_strictMono
    (fun B : IrreducibleCloseds X.carrier => OrderDual.toDual (X.supportCodimension B))
    (Supports.codimension_strictAnti X m) A
  simpa only [CycleClass.Thom.IntersectionGeometry.supportPoint, coheight_orderIso, coheight_toDual, height_nat] using h

theorem coheight_one (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] (A : X.DimensionCycleSupport 1) :
    coheight (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) = 1 := by
  apply le_antisymm
  · simpa only [A.property, Nat.cast_one] using coheight_le_codimension X m A.val
  · let C := ZeroComponents.containingComponent X m A.val
    have hlt : A.val < C.val := lt_of_le_of_ne
      (ZeroComponents.subset_containingComponent X m A.val) (by
        intro he
        have h := congrArg X.supportCodimension he
        rw [A.property, C.property] at h
        omega)
    rw [CycleClass.Thom.IntersectionGeometry.supportPoint, coheight_orderIso]
    exact (le_add_self : (1 : ℕ∞) ≤ coheight C.val + 1).trans (coheight_add_one_le hlt)

theorem support_eq_singleton (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    [SmoothOfRelativeDimension 1 X.structureMap] (A : X.DimensionCycleSupport 1) :
    (A.val : Set X.carrier) = {CycleClass.Thom.IntersectionGeometry.supportPoint A.val} := by
  apply Set.Subset.antisymm
  · intro x hx
    let B : IrreducibleCloseds X.carrier := irreducibleSetEquivPoints.symm x
    have hBA : B ≤ A.val := A.val.isClosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hx)
    have he : B = A.val := by
      by_contra hn
      have h := Supports.codimension_strictAnti X 1 (lt_of_le_of_ne hBA hn)
      rw [A.property] at h
      have hb := codimension_le X 1 B
      omega
    exact Set.mem_singleton_iff.mpr
      ((irreducibleSetEquivPoints.apply_symm_apply x).symm.trans (congrArg CycleClass.Thom.IntersectionGeometry.supportPoint he))
  · exact Set.singleton_subset_iff.mpr
      (A.val.isIrreducible.isGenericPoint_genericPoint A.val.isClosed).mem

theorem no_support_above_dimension (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] (hp : m < p) :
    IsEmpty (X.DimensionCycleSupport p) := by
  refine ⟨fun A => ?_⟩
  have h := codimension_le X m A.val
  rw [A.property] at h
  omega

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CurveSupports
