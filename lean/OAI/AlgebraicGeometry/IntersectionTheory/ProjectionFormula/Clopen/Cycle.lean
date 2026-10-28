import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IntermediateSupports
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity

/-! # Cycle -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Clopen.Cycle

noncomputable section

/-! Actual support images and inverse images for open and closed
immersions preserve every codimension. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace _root_.Order

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity

variable {V X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}

theorem image_point (i : V.toOver ⟶ X.toOver) (W : IrreducibleCloseds V.carrier) :
    CycleClass.Thom.IntersectionGeometry.supportPoint (ProperCycleLinearity.imageSupport i W) = i.left (CycleClass.Thom.IntersectionGeometry.supportPoint W) := irreducibleSetEquivPoints.apply_symm_apply _

def preimage (i : V.toOver ⟶ X.toOver) (W : IrreducibleCloseds X.carrier)
    (hW : (W : Set X.carrier) ⊆ Set.range i.left) : IrreducibleCloseds V.carrier :=
  irreducibleSetEquivPoints.symm
    (hW (W.isIrreducible.isGenericPoint_genericPoint W.isClosed).mem).choose

theorem image_preimage (i : V.toOver ⟶ X.toOver) (W : IrreducibleCloseds X.carrier)
    (hW : (W : Set X.carrier) ⊆ Set.range i.left) : ProperCycleLinearity.imageSupport i (preimage i W hW) = W := by
  apply irreducibleSetEquivPoints.injective
  change CycleClass.Thom.IntersectionGeometry.supportPoint (ProperCycleLinearity.imageSupport i (preimage i W hW)) = CycleClass.Thom.IntersectionGeometry.supportPoint W
  rw [image_point]
  change i.left (irreducibleSetEquivPoints (irreducibleSetEquivPoints.symm _)) = _
  rw [irreducibleSetEquivPoints.apply_symm_apply]
  exact (hW (W.isIrreducible.isGenericPoint_genericPoint W.isClosed).mem).choose_spec

theorem preimage_coe (i : V.toOver ⟶ X.toOver) [IsOpenImmersion i.left]
    (W : IrreducibleCloseds X.carrier) (hW : (W : Set X.carrier) ⊆ Set.range i.left) :
    (preimage i W hW : Set V.carrier) = i.left ⁻¹' (W : Set X.carrier) := by
  conv_rhs => rw [← image_preimage i W hW, ProperCycleLinearity.imageSupport_eq_image]
  exact (Set.preimage_image_eq _ i.left.isOpenEmbedding.injective).symm

theorem subset_range_of_mem (i : V.toOver ⟶ X.toOver) [IsOpenImmersion i.left] [IsClosedImmersion i.left]
    (W : IrreducibleCloseds X.carrier) (x : X.carrier) (hx : x ∈ (W : Set X.carrier))
    (hi : x ∈ Set.range i.left) : (W : Set X.carrier) ⊆ Set.range i.left := by
  have hη := ((W.isIrreducible.isGenericPoint_genericPoint W.isClosed).specializes hx).mem_open
    i.left.isOpenEmbedding.isOpen_range hi
  intro y hy
  exact ((W.isIrreducible.isGenericPoint_genericPoint W.isClosed).specializes hy).mem_closed
    i.left.isClosedEmbedding.isClosed_range hη

theorem image_codimension (i : V.toOver ⟶ X.toOver) [IsOpenImmersion i.left] (m : ℕ)
    [SmoothOfRelativeDimension m V.structureMap] [SmoothOfRelativeDimension m X.structureMap]
    (W : IrreducibleCloseds V.carrier) : X.supportCodimension (ProperCycleLinearity.imageSupport i W) = V.supportCodimension W := by
  have hv := IntermediateSupports.support_coheight V m (V.supportCodimension W) ⟨W, rfl⟩
  have hx := IntermediateSupports.support_coheight X m (X.supportCodimension (ProperCycleLinearity.imageSupport i W)) ⟨_, rfl⟩
  have hi : coheight (CycleClass.Thom.IntersectionGeometry.supportPoint (ProperCycleLinearity.imageSupport i W)) = coheight (CycleClass.Thom.IntersectionGeometry.supportPoint W) := by
    rw [image_point, coheight_eq_of_isOpenImmersion i.left]
  exact_mod_cast hx.symm.trans (hi.trans hv)

def supportImage (i : V.toOver ⟶ X.toOver) [IsOpenImmersion i.left] (m p : ℕ)
    [SmoothOfRelativeDimension m V.structureMap] [SmoothOfRelativeDimension m X.structureMap]
    (A : V.DimensionCycleSupport p) : X.DimensionCycleSupport p :=
  ⟨ProperCycleLinearity.imageSupport i A.val, (image_codimension i m A.val).trans A.property⟩

theorem supportImage_injective (i : V.toOver ⟶ X.toOver) [IsOpenImmersion i.left] (m p : ℕ)
    [SmoothOfRelativeDimension m V.structureMap] [SmoothOfRelativeDimension m X.structureMap] :
    Function.Injective (supportImage i m p) := by
  intro A B h
  apply Subtype.ext
  apply irreducibleSetEquivPoints.injective
  apply i.left.isOpenEmbedding.injective
  exact (image_point i A.val).symm.trans
    ((congrArg (fun C : X.DimensionCycleSupport p => CycleClass.Thom.IntersectionGeometry.supportPoint C.val) h).trans (image_point i B.val))

def supportPreimage (i : V.toOver ⟶ X.toOver) [IsOpenImmersion i.left] (m p : ℕ)
    [SmoothOfRelativeDimension m V.structureMap] [SmoothOfRelativeDimension m X.structureMap]
    (A : X.DimensionCycleSupport p) (hA : (A.val : Set X.carrier) ⊆ Set.range i.left) :
    V.DimensionCycleSupport p :=
  ⟨preimage i A.val hA, by rw [← image_codimension i m, image_preimage, A.property]⟩

theorem supportImage_preimage (i : V.toOver ⟶ X.toOver) [IsOpenImmersion i.left] (m p : ℕ)
    [SmoothOfRelativeDimension m V.structureMap] [SmoothOfRelativeDimension m X.structureMap]
    (A : X.DimensionCycleSupport p) (hA : (A.val : Set X.carrier) ⊆ Set.range i.left) :
    supportImage i m p (supportPreimage i m p A hA) = A := Subtype.ext (image_preimage i A.val hA)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Clopen.Cycle
