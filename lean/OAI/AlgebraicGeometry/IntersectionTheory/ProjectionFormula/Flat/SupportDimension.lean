import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NestedSupportCoheight
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Generic.SmoothMorphism
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Flat.ImageCodimension
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Map

/-! # Support Dimension -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Flat.SupportDimension

noncomputable section

/-! On the smooth open of the actual map between reduced supports,
flatness bounds the source codimension by the target codimension.
This is the dimension estimate used in relative proper positioning. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace _root_.Order

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Map

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver)
  (m n : ℕ) [SmoothOfRelativeDimension m X.structureMap] [SmoothOfRelativeDimension n Y.structureMap]

include m n in
theorem at_smooth (W C : IrreducibleCloseds X.carrier) (hCW : C ≤ W)
    (hx : CycleClass.Thom.IntersectionGeometry.supportPreimage W (CycleClass.Thom.IntersectionGeometry.supportPoint C)
      (hCW (C.isIrreducible.isGenericPoint_genericPoint C.isClosed).mem) ∈ (Support.Map.supportImageMap f W).smoothLocus) :
    X.supportCodimension W + Y.supportCodimension (ProperCycleLinearity.imageSupport f C) ≤
      X.supportCodimension C + Y.supportCodimension (ProperCycleLinearity.imageSupport f W) := by
  let V := ProperCycleLinearity.imageSupport f W
  let D := ProperCycleLinearity.imageSupport f C
  let u := Support.Map.supportImageMap f W
  let x := CycleClass.Thom.IntersectionGeometry.supportPreimage W (CycleClass.Thom.IntersectionGeometry.supportPoint C) (hCW (C.isIrreducible.isGenericPoint_genericPoint C.isClosed).mem)
  have hDV : D ≤ V := by
    change (ProperCycleLinearity.imageSupport f C : Set Y.carrier) ⊆ ProperCycleLinearity.imageSupport f W
    rw [ProperCycleLinearity.imageSupport_eq_image, ProperCycleLinearity.imageSupport_eq_image]
    exact Set.image_mono hCW
  let y := CycleClass.Thom.IntersectionGeometry.supportPreimage V (CycleClass.Thom.IntersectionGeometry.supportPoint D) (hDV (D.isIrreducible.isGenericPoint_genericPoint D.isClosed).mem)
  have hy : u x = y := by
    apply (CycleClass.Geometric.GenericPoint.reducedSupportι V).isEmbedding.injective
    rw [CycleClass.Thom.IntersectionGeometry.supportPreimage_spec]
    have h := congrArg (fun g : CycleClass.Geometric.GenericPoint.reducedSupportScheme W ⟶ Y.carrier => g x) (Support.Map.supportImageMap_inclusion f W)
    change CycleClass.Geometric.GenericPoint.reducedSupportι V (u x) = f.left (CycleClass.Geometric.GenericPoint.reducedSupportι W x) at h
    rw [CycleClass.Thom.IntersectionGeometry.supportPreimage_spec] at h
    exact h.trans (irreducibleSetEquivPoints.apply_symm_apply _).symm
  let U := u.smoothLocus
  let x' : U.toScheme := ⟨x, hx⟩
  let : Smooth (U.ι ≫ u) := Generic.SmoothMorphism.smooth_restrict u
  have hx' : coheight x' = (X.supportCodimension C - X.supportCodimension W : ℕ) :=
    (show coheight (U.ι x') = coheight x' from coheight_eq_of_isOpenImmersion U.ι).symm.trans
      (NestedSupportCoheight.difference X m W C hCW)
  have hc := ImageCodimension.coheight_le (U.ι ≫ u)
    (X.supportCodimension C - X.supportCodimension W) x' hx'.le
  change coheight (u x) ≤ (X.supportCodimension C - X.supportCodimension W : ℕ) at hc
  rw [hy, NestedSupportCoheight.difference Y n V D hDV] at hc
  have hd : Y.supportCodimension D - Y.supportCodimension V ≤
      X.supportCodimension C - X.supportCodimension W := by exact_mod_cast hc
  have hX := (Supports.codimension_strictAnti X m).antitone hCW
  have hY := (Supports.codimension_strictAnti Y n).antitone hDV
  change X.supportCodimension W + Y.supportCodimension D ≤ X.supportCodimension C + Y.supportCodimension V
  omega

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Flat.SupportDimension
