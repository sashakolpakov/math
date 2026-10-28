import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Integral.DivisorThroughPoint
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.DivisorImage

/-! # Intermediate Supports -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IntermediateSupports

noncomputable section

/-! Actual intermediate integral supports exist in every lower
codimension. Consequently native specialization coheight agrees with the
dimension grading at every support, in every ambient dimension. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace _root_.Order

theorem image_mem (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (W : IrreducibleCloseds X.carrier)
    (Z : IrreducibleCloseds (CycleClass.Geometric.GenericPoint.reducedSupportScheme W)) (y : CycleClass.Geometric.GenericPoint.reducedSupportScheme W)
    (hy : y ∈ (Z : Set (CycleClass.Geometric.GenericPoint.reducedSupportScheme W))) :
    CycleClass.Geometric.GenericPoint.reducedSupportι W y ∈ (Support.DivisorImage.image X W Z : Set X.carrier) := by
  have hs := ((Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed).specializes hy).map
    (CycleClass.Geometric.GenericPoint.reducedSupportι W).continuous
  change CycleClass.Geometric.GenericPoint.reducedSupportι W (CycleClass.Thom.IntersectionGeometry.supportPoint Z) ⤳ CycleClass.Geometric.GenericPoint.reducedSupportι W y at hs
  rw [← Support.DivisorImage.image_point X W Z] at hs
  exact hs.mem_closed (Support.DivisorImage.image X W Z).isClosed
    ((Support.DivisorImage.image X W Z).isIrreducible.isGenericPoint_genericPoint
      (Support.DivisorImage.image X W Z).isClosed).mem

theorem next_support (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m r p : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (W : X.DimensionCycleSupport r) (C : X.DimensionCycleSupport p)
    (hr : r < p) (hCW : C.val ≤ W.val) :
    ∃ A : X.DimensionCycleSupport (r + 1), C.val ≤ A.val ∧ A.val ≤ W.val := by
  have hxW : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (W.val : Set X.carrier) :=
    hCW (C.val.isIrreducible.isGenericPoint_genericPoint C.val.isClosed).mem
  let y := CycleClass.Thom.IntersectionGeometry.supportPreimage W.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxW
  have hy : y ≠ genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val) := by
    intro he
    have hpnt := congrArg (CycleClass.Geometric.GenericPoint.reducedSupportι W.val) he
    rw [CycleClass.Thom.IntersectionGeometry.supportPreimage_spec, CycleClass.Geometric.GenericPoint.reducedSupport_genericPoint_eq] at hpnt
    have hd := congrArg X.supportCodimension (irreducibleSetEquivPoints.injective hpnt)
    rw [C.property, W.property] at hd
    omega
  obtain ⟨Z, hZ, hyZ⟩ := Integral.DivisorThroughPoint.exists_support (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val) y hy
  let A := Support.DivisorImage.image X W.val Z
  have hA : X.supportCodimension A = r + 1 := by
    rw [Support.DivisorImage.codimension X W.val m Z hZ, W.property]
  refine ⟨⟨A, hA⟩, ?_, Support.DivisorImage.image_le X W.val Z⟩
  apply (Supports.supportPoint_mem_iff_subset
    (⟨(A : Set X.carrier), A.isClosed⟩ : Closeds X.carrier) C.val).mp
  have h := image_mem X W.val Z y hyZ
  rw [CycleClass.Thom.IntersectionGeometry.supportPreimage_spec] at h
  exact h

theorem exists_support (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m r p : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] (C : X.DimensionCycleSupport p) (hr : r ≤ p) :
    ∃ A : X.DimensionCycleSupport r, C.val ≤ A.val := by
  induction r with
  | zero =>
    exact ⟨ZeroComponents.containingComponent X m C.val,
      ZeroComponents.subset_containingComponent X m C.val⟩
  | succ r ih =>
    obtain ⟨W, hCW⟩ := ih (by omega)
    obtain ⟨A, hCA, _⟩ := next_support X m r p W C (by omega) hCW
    exact ⟨A, hCA⟩

theorem support_coheight (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] (C : X.DimensionCycleSupport p) :
    coheight (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) = p := by
  induction p with
  | zero =>
    have h := CurveSupports.coheight_le_codimension X m C.val
    rw [C.property, Nat.cast_zero] at h
    exact le_antisymm h zero_le
  | succ p ih =>
    obtain ⟨A, hCA⟩ := exists_support X m p (p + 1) C (by omega)
    have hne : C.val ≠ A.val := by
      intro he
      have h := congrArg X.supportCodimension he
      rw [C.property, A.property] at h
      omega
    have hA : coheight A.val = p := by simpa only [CycleClass.Thom.IntersectionGeometry.supportPoint, coheight_orderIso] using ih A
    apply le_antisymm
    · simpa only [C.property] using CurveSupports.coheight_le_codimension X m C.val
    · rw [CycleClass.Thom.IntersectionGeometry.supportPoint, coheight_orderIso]
      simpa only [hA, Nat.cast_add, Nat.cast_one] using coheight_add_one_le (lt_of_le_of_ne hCA hne)

theorem stalk_height (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] (C : X.DimensionCycleSupport p) :
    (IsLocalRing.maximalIdeal (X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val))).height = p := by
  apply WithBot.coe_injective
  rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim, ringKrullDim_stalk_eq_coheight,
    support_coheight X m p C]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IntermediateSupports
