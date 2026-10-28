/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
This file has been modified.
-/
import OAI.AlgebraicGeometry.ClosedImmersion.HolomorphicCharts

/-! # Holomorphic Charts At -/

namespace OAI.AlgebraicGeometry.ClosedImmersion.HolomorphicChartsAt

noncomputable section

open _root_.AlgebraicGeometry
open _root_.OpenPartialHomeomorph

/-!
# Holomorphic support-flattening charts

-/

/-! ### Constructions used only in proofs -/

section

open _root_.CategoryTheory _root_.Topology Filter

namespace OpenPartialHomeomorph

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace E] [CompleteSpace F]
  (e : OpenPartialHomeomorph E F)

theorem biAnalyticRestrict_mem_source_iff (x : E) :
    x ∈ (HolomorphicCharts.OpenPartialHomeomorph.biAnalyticRestrict e).source ↔
      x ∈ e.source ∧ AnalyticAt ℂ e x ∧ AnalyticAt ℂ e.symm (e x) := by
  change (x ∈ e.source ∧ AnalyticAt ℂ e x ∧ x ∈ e.source ∧ AnalyticAt ℂ e.symm (e x)) ↔ _
  aesop

end OpenPartialHomeomorph

namespace ComplexPoint
open OAI.AlgebraicTopology.Singular
section

variable (X Y : Over (Spec ↧ℂ))
  (i : Y ⟶ X) (m d : ℕ)
  [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
  [IsClosedImmersion i.left] (z : ComplexPoint.Basic.ComplexSchemePoint Y)

theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart_mem_range_iff (y : ComplexPoint.Basic.ComplexSchemePoint X)
    (hy : y ∈ (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart X Y i m d z).source) :
    y ∈ Set.range (ComplexPoint.Basic.Point.map i) ↔
      (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart X Y i m d z y).2 = 0 :=
  ComplexPoint.Basic.ComplexSchemePoint.closedImmersionStandardFlatteningChart_mem_range_iff X Y i m d z y hy.2

end

variable (X Y : Over (Spec ↧ℂ))
  (i : Y ⟶ X) (m d : ℕ)
  [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
  [IsClosedImmersion i.left] (z : ComplexPoint.Basic.ComplexSchemePoint Y)

/-- The underlying normal coordinate change and its inverse are analytic at every ambient
source point. -/
private theorem closedImmersionHolomorphicFlatteningChart_analytic (y : ComplexPoint.Basic.ComplexSchemePoint X)
    (hy : y ∈ (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart X Y i m d z).source) :
    AnalyticAt ℂ (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalCoordinateChange X Y i m d z)
      (ComplexPoint.Basic.ComplexSchemePoint.localChart X d (ComplexPoint.Basic.Point.map i z) y) ∧
    AnalyticAt ℂ (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalCoordinateChange X Y i m d z).symm
      (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart X Y i m d z y) :=
  ((HolomorphicChartsAt.OpenPartialHomeomorph.biAnalyticRestrict_mem_source_iff _ _).mp hy.1.2).2

private theorem closedImmersionNormalCoordinateChange_symm_at_chart (y : ComplexPoint.Basic.ComplexSchemePoint X)
    (hy : y ∈ (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart X Y i m d z).source) :
    (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalCoordinateChange X Y i m d z).symm
      (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart X Y i m d z y) =
        ComplexPoint.Basic.ComplexSchemePoint.localChart X d (ComplexPoint.Basic.Point.map i z) y :=
  (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalCoordinateChange X Y i m d z).left_inv hy.1.2.1

variable (z' : ComplexPoint.Basic.ComplexSchemePoint Y)

/-- Let `i: Y → X` be a closed immersion of smooth schemes over `ℂ` of dimensions `m` and `d`,
respectively. Choose points `z,z′ ∈ Y(ℂ)` and their holomorphic charts `e_z,e_z′` in `ℂ^m ×
ℂ^{d-m}` that identify the image of `Y(ℂ)` with the locus where the second coordinate is zero.
This local homeomorphism is the coordinate change `e_z′ ∘ e_z⁻¹` on the overlap. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalTransition :
    OpenPartialHomeomorph ((Fin m → ℂ) × (Fin (d - m) → ℂ))
      ((Fin m → ℂ) × (Fin (d - m) → ℂ)) :=
  (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart X Y i m d z).symm.trans
    (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart X Y i m d z')

/-- These transitions are holomorphic throughout their domains. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticAt_closedImmersionNormalTransition
    (v : (Fin m → ℂ) × (Fin (d - m) → ℂ))
    (hv : v ∈ (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalTransition X Y i m d z z').source) :
    AnalyticAt ℂ (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalTransition X Y i m d z z') v := by
  let e := ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart X Y i m d z
  let e' := ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart X Y i m d z'
  let C := ComplexPoint.Basic.ComplexSchemePoint.localChart X d (ComplexPoint.Basic.Point.map i z)
  let C' := ComplexPoint.Basic.ComplexSchemePoint.localChart X d (ComplexPoint.Basic.Point.map i z')
  let A := ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalCoordinateChange X Y i m d z
  let A' := ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalCoordinateChange X Y i m d z'
  let y := e.symm v
  have hyv : y ∈ e.source := e.map_target hv.1
  have hyv' : y ∈ e'.source := hv.2
  have hyC : y ∈ C.source := hyv.1.1
  have hyC' : y ∈ C'.source := hyv'.1.1
  have hAv := closedImmersionNormalCoordinateChange_symm_at_chart
    X Y i m d z y hyv
  rw [e.right_inv hv.1] at hAv
  have hA := (closedImmersionHolomorphicFlatteningChart_analytic
    X Y i m d z y hyv).2
  rw [e.right_inv hv.1] at hA
  have hA' := (closedImmersionHolomorphicFlatteningChart_analytic
    X Y i m d z' y hyv').1
  have hCC : AnalyticAt ℂ (fun w => C' (C.symm w)) (C y) := by
    apply ComplexPoint.Basic.ComplexSchemePoint.analyticAt_localChart_transition X d (ComplexPoint.Basic.Point.map i z) (ComplexPoint.Basic.Point.map i z')
    refine ⟨C.map_source hyC, ?_⟩
    change C.symm (C y) ∈ C'.source
    rw [C.left_inv hyC]
    exact hyC'
  have hCC' : AnalyticAt ℂ (fun w => C' (C.symm w)) (A.symm v) := hAv ▸ hCC
  have hmiddle := hCC'.comp hA
  have himage : C' (C.symm (A.symm v)) = C' y := by rw [hAv, C.left_inv hyC]
  have hlast : AnalyticAt ℂ A' (C' (C.symm (A.symm v))) := himage ▸ hA'
  exact hlast.comp (f := fun w => C' (C.symm (A.symm w))) (x := v) hmiddle

/-- The inverse transition is holomorphic at the image of every source point. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticAt_closedImmersionNormalTransition_symm
    (v : (Fin m → ℂ) × (Fin (d - m) → ℂ))
    (hv : v ∈ (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalTransition X Y i m d z z').source) :
    AnalyticAt ℂ (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalTransition X Y i m d z z').symm
      (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalTransition X Y i m d z z' v) :=
  ComplexPoint.Basic.ComplexSchemePoint.analyticAt_closedImmersionNormalTransition X Y i m d z' z
    (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalTransition X Y i m d z z' v)
    ((ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalTransition X Y i m d z z').map_source hv)

end ComplexPoint

end

open _root_.CategoryTheory _root_.Topology Filter

namespace OpenPartialHomeomorph

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace E] [CompleteSpace F]
  (e : OpenPartialHomeomorph E F)

@[simp] theorem biAnalyticRestrict_apply (x : E) : (HolomorphicCharts.OpenPartialHomeomorph.biAnalyticRestrict e) x = e x := rfl
@[simp] theorem biAnalyticRestrict_symm_apply (y : F) : (HolomorphicCharts.OpenPartialHomeomorph.biAnalyticRestrict e).symm y = e.symm y := rfl

end OpenPartialHomeomorph

namespace ComplexPoint

open OAI.AlgebraicTopology.Singular

variable (X Y : Over (Spec ↧ℂ))
  (i : Y ⟶ X) (m d : ℕ)
  [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
  [IsClosedImmersion i.left] (z : ComplexPoint.Basic.ComplexSchemePoint Y)

theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalCoordinateChange_mem_source :
    ComplexPoint.Basic.ComplexSchemePoint.localChart X d (ComplexPoint.Basic.Point.map i z) (ComplexPoint.Basic.Point.map i z) ∈
      (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalCoordinateChange X Y i m d z).source :=
  ⟨ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalChart_mem_target X Y i m d z, trivial⟩

@[simp] theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalCoordinateChange_center :
    ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalCoordinateChange X Y i m d z
      (ComplexPoint.Basic.ComplexSchemePoint.localChart X d (ComplexPoint.Basic.Point.map i z) (ComplexPoint.Basic.Point.map i z)) =
        (ComplexPoint.Basic.ComplexSchemePoint.localChart Y m z z, 0) := by
  change ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalCoordinatesLinearEquiv X Y i m d z
    ((ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalChart X Y i m d z).symm _) = _
  simp [ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalCoordinatesLinearEquiv]

theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticAt_closedImmersionNormalCoordinateChange :
    AnalyticAt ℂ (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalCoordinateChange X Y i m d z)
      (ComplexPoint.Basic.ComplexSchemePoint.localChart X d (ComplexPoint.Basic.Point.map i z) (ComplexPoint.Basic.Point.map i z)) :=
  ((ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalCoordinatesLinearEquiv X Y i m d z).toContinuousLinearMap.analyticAt
    _).comp (ComplexPoint.Basic.ComplexSchemePoint.analyticAt_closedImmersionNormalChart_symm X Y i m d z)

theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.analyticAt_closedImmersionNormalCoordinateChange_symm :
    AnalyticAt ℂ (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalCoordinateChange X Y i m d z).symm
      (ComplexPoint.Basic.ComplexSchemePoint.localChart Y m z z, 0) := by
  let K := ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalCoordinatesLinearEquiv X Y i m d z
  have hK : K.symm (ComplexPoint.Basic.ComplexSchemePoint.localChart Y m z z, 0) = (ComplexPoint.Basic.ComplexSchemePoint.localChart Y m z z, 0) := by
    simp [K, ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalCoordinatesLinearEquiv]
  have hA' : AnalyticAt ℂ (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalChart X Y i m d z)
      (K.symm (ComplexPoint.Basic.ComplexSchemePoint.localChart Y m z z, 0)) := hK ▸ ComplexPoint.Basic.ComplexSchemePoint.analyticAt_closedImmersionNormalChart X Y i m d z
  exact hA'.comp (K.symm.toContinuousLinearMap.analyticAt _)

@[simp] theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart_apply (y : ComplexPoint.Basic.ComplexSchemePoint X) :
    ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart X Y i m d z y =
      ComplexPoint.Basic.ComplexSchemePoint.closedImmersionStandardFlatteningChart X Y i m d z y := rfl

@[simp] theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart_symm_apply
    (v : (Fin m → ℂ) × (Fin (d - m) → ℂ)) :
    (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart X Y i m d z).symm v =
      (ComplexPoint.Basic.ComplexSchemePoint.localChart X d (ComplexPoint.Basic.Point.map i z)).symm
        ((ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalCoordinateChange X Y i m d z).symm v) := rfl

theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart_mem_source :
    ComplexPoint.Basic.Point.map i z ∈
      (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart X Y i m d z).source := by
  refine ⟨⟨ComplexPoint.Basic.ComplexSchemePoint.mem_localChart_source X d (ComplexPoint.Basic.Point.map i z), ?_⟩,
    ComplexPoint.Basic.ComplexSchemePoint.closedImmersionStandardFlatteningChart_mem_source X Y i m d z⟩
  apply (HolomorphicChartsAt.OpenPartialHomeomorph.biAnalyticRestrict_mem_source_iff _ _).mpr
  refine ⟨ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalCoordinateChange_mem_source X Y i m d z,
    ComplexPoint.Basic.ComplexSchemePoint.analyticAt_closedImmersionNormalCoordinateChange X Y i m d z, ?_⟩
  simp only [OpenPartialHomeomorph.symm_symm]
  rw [ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalCoordinateChange_center]
  exact ComplexPoint.Basic.ComplexSchemePoint.analyticAt_closedImmersionNormalCoordinateChange_symm X Y i m d z

@[simp] theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart_center :
    ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart X Y i m d z (ComplexPoint.Basic.Point.map i z) =
      (ComplexPoint.Basic.ComplexSchemePoint.localChart Y m z z, 0) :=
  ComplexPoint.Basic.ComplexSchemePoint.closedImmersionStandardFlatteningChart_center X Y i m d z

end ComplexPoint

end

end OAI.AlgebraicGeometry.ClosedImmersion.HolomorphicChartsAt
