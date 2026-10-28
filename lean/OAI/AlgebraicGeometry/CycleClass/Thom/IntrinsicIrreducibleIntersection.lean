import OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectiveSupportIsolation

/-! # Intrinsic Irreducible Intersection -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicIrreducibleIntersection.Constructions.Intrinsic

noncomputable section

/-! A one-component proper intersection in the native integral-variety
grading has precisely its genuine local Serre coefficient. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectiveSupportIsolation.Constructions.Intersection OAI.AlgebraicGeometry.CycleClass.Thom.Supported.Map.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.Supports

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p q : ℕ}
  (A : Geometric.DimensionCycles.DimensionCycleSupport V p) (B : Geometric.DimensionCycles.DimensionCycleSupport V q)
  (C : Geometric.DimensionCycles.DimensionCycleSupport V (p + q))
  (hC : (C.val : Set V.carrier) = (A.val : Set V.carrier) ∩ (B.val : Set V.carrier))

include hC in
theorem intersection_dimension_bound (Z : IrreducibleCloseds V.carrier)
    (hZ : (Z : Set V.carrier) ⊆ Supported.ProjectiveSupportIsolation.Constructions.Intersection.intersectionClosed V p q A B) :
    p + q ≤ Geometric.DimensionCycles.dimensionCodimension V Z := by
  have hZC : Z ≤ C.val := by
    change (Z : Set V.carrier) ⊆ (C.val : Set V.carrier)
    rw [hC]
    exact hZ
  rw [← C.property]
  exact Nat.sub_le_sub_left ((Foundations.Scheme.SupportDimensionDrop.supportTranscendenceDimension_strictMono V.structureMap).monotone hZC) _

include hC in
theorem multiplicity_eq_zero_of_ne (D : Geometric.DimensionCycles.DimensionCycleSupport V (p + q)) (hD : D ≠ C) :
    IntersectionGeometry.intersectionMultiplicity V.presentation A.val B.val D.val = 0 := by
  apply dite_eq_right
  intro hx
  have hDC : D.val ≤ C.val := by
    apply (Intersection.Supports.supportPoint_mem_iff_subset (⟨C.val, C.val.isClosed⟩ : Closeds V.carrier) D.val).mp
    change IntersectionGeometry.supportPoint D.val ∈ (C.val : Set V.carrier)
    rwa [hC]
  have hne : D.val ≠ C.val := fun h => hD (Subtype.ext h)
  have ht := Foundations.Scheme.SupportDimensionDrop.supportTranscendenceDimension_lt_of_lt D.val C.val V.structureMap
    (lt_of_le_of_ne hDC hne)
  have h₁ := Geometric.DimensionCycles.supportDimension_add_dimensionCodimension V D.val
  have h₂ := Geometric.DimensionCycles.supportDimension_add_dimensionCodimension V C.val
  rw [D.property] at h₁
  rw [C.property] at h₂
  omega

include hC in
theorem supportedPairCycle_forget_eq_single
    (hproper : ∀ Z : IrreducibleCloseds V.carrier,
      (Z : Set V.carrier) ⊆ Supported.ProjectiveSupportIsolation.Constructions.Intersection.intersectionClosed V p q A B → p + q ≤ Geometric.DimensionCycles.dimensionCodimension V Z) :
    Supported.Map.Constructions.forgetCycle V (Supported.ProjectiveSupportIsolation.Constructions.Intersection.intersectionClosed V p q A B) (p + q)
      (Supported.ProjectiveSupportIsolation.Constructions.Intersection.supportedPairCycle V p q A B hproper) =
      Finsupp.single C (IntersectionGeometry.intersectionMultiplicity V.presentation A.val B.val C.val) := by
  classical
  ext D
  rw [Supported.ProjectiveSupportIsolation.Constructions.Intersection.supportedPairCycle_forget_coefficient]
  by_cases hD : D = C
  · subst D
    simp only [Finsupp.single_eq_same]
  · rw [multiplicity_eq_zero_of_ne A B C hC D hD, Finsupp.single_eq_of_ne hD]

end

end OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicIrreducibleIntersection.Constructions.Intrinsic
