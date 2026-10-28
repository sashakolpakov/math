import OAI.AlgebraicGeometry.SheafCohomology.TensorBundles
import OAI.AlgebraicGeometry.SheafCohomology.TensorFrames

/-! # Tensor Coordinates -/

namespace OAI.AlgebraicGeometry.SheafCohomology.TensorCoordinates.Projective

noncomputable section

/-! Coordinates of the constructed local tensor frame on pure tensors. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

variable (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (U : A.carrier.Opens)
variable (M N : SheafOfModules.{0} (A.carrier.ringCatSheaf.over U))
variable (e : M ≅ SheafOfModules.unit (A.carrier.ringCatSheaf.over U))
variable (f : N ≅ SheafOfModules.unit (A.carrier.ringCatSheaf.over U))

def localTensorFrame : TensorBundles.Projective.localTensor A U M N ≅ SheafOfModules.unit
    (A.carrier.ringCatSheaf.over U) :=
  TensorBundles.Projective.localTensorIso A U e f ≪≫ TensorBundles.Projective.localTensorUnitIso A U

def tensorPresheafFrame :
    PresheafOfModulesOfCommRing.Monoidal.tensorObj
        (R := (Over.forget U).op ⋙ A.carrier.presheaf) M.val N.val ⟶
      (SheafOfModules.unit (A.carrier.ringCatSheaf.over U)).val :=
  PresheafOfModulesOfCommRing.Monoidal.tensorHom
      (R := (Over.forget U).op ⋙ A.carrier.presheaf) e.hom.val f.hom.val ≫
    (MonoidalCategory.leftUnitor
      (C := PresheafOfModules.{0}
        (((Over.forget U).op ⋙ A.carrier.presheaf) ⋙ forget₂ CommRingCat RingCat))
      (SheafOfModules.unit (A.carrier.ringCatSheaf.over U)).val).hom

set_option backward.isDefEq.respectTransparency false in
theorem localTensorFrame_eq_adjunct :
    (localTensorFrame A U M N e f).hom =
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 (A.carrier.ringCatSheaf.over U).obj)).homEquiv _ _).symm
          (tensorPresheafFrame A U M N e f) := by
  erw [Adjunction.homEquiv_counit]
  unfold localTensorFrame TensorBundles.Projective.localTensorIso TensorBundles.Projective.localTensorUnitIso tensorPresheafFrame
  simp only [Iso.trans_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  rfl

/-- On the presheaf before sheafification, the actual sheaf frame is the
product of the original coordinates. -/
theorem localTensorFrame_unit :
    (PresheafOfModules.sheafificationAdjunction
        (𝟙 (A.carrier.ringCatSheaf.over U).obj)).unit.app
        (PresheafOfModulesOfCommRing.Monoidal.tensorObj
          (R := (Over.forget U).op ⋙ A.carrier.presheaf) M.val N.val) ≫
      (localTensorFrame A U M N e f).hom.val = tensorPresheafFrame A U M N e f := by
  change ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (A.carrier.ringCatSheaf.over U).obj)).homEquiv _ _)
    (localTensorFrame A U M N e f).hom = _
  erw [localTensorFrame_eq_adjunct]
  exact Equiv.apply_symm_apply _ _

set_option backward.isDefEq.respectTransparency false in
/-- The section coordinates of a pure tensor multiply. Both the tensor
section and the frame are the actual maps through sheafification. -/
theorem localTensorFrame_unit_tmul (V : Over U)
    (m : M.val.obj (Opposite.op V)) (n : N.val.obj (Opposite.op V)) :
    (localTensorFrame A U M N e f).hom.val.app (Opposite.op V)
      (((PresheafOfModules.sheafificationAdjunction
          (𝟙 (A.carrier.ringCatSheaf.over U).obj)).unit.app
          (PresheafOfModulesOfCommRing.Monoidal.tensorObj
            (R := (Over.forget U).op ⋙ A.carrier.presheaf) M.val N.val)).app
        (Opposite.op V) (m ⊗ₜ[Γ(A.carrier, V.left)] n)) =
      @HMul.hMul Γ(A.carrier, V.left) Γ(A.carrier, V.left) Γ(A.carrier, V.left)
        inferInstance (e.hom.val.app (Opposite.op V) m)
          (f.hom.val.app (Opposite.op V) n) := by
  have h := congrArg (fun k => k.app (Opposite.op V))
    (localTensorFrame_unit A U M N e f)
  have hm := congrArg (fun k => k (m ⊗ₜ[Γ(A.carrier, V.left)] n)) h
  exact hm.trans (by rfl)

set_option backward.isDefEq.respectTransparency false in
/-- Evaluating a sheaf frame gives a linear frame of its module of sections. -/
def sliceSectionFrame (V : Over U) :
    M.val.obj (Opposite.op V) ≃ₗ[Γ(A.carrier, V.left)] Γ(A.carrier, V.left) :=
  ((SheafOfModules.evaluation (A.carrier.ringCatSheaf.over U)
    (Opposite.op V)).mapIso e).toLinearEquiv

set_option backward.isDefEq.respectTransparency false in
/-- The actual sheaf tensor frames have the product transition unit on
every object of the slice site. -/
theorem localTensorSectionFrame_transition
    (e' : M ≅ SheafOfModules.unit (A.carrier.ringCatSheaf.over U))
    (f' : N ≅ SheafOfModules.unit (A.carrier.ringCatSheaf.over U)) (V : Over U) :
    DivisorClass.Chern.FramesFrame.Construction.frameTransitionUnit
      (sliceSectionFrame A U (TensorBundles.Projective.localTensor A U M N) (localTensorFrame A U M N e f) V)
      (sliceSectionFrame A U (TensorBundles.Projective.localTensor A U M N) (localTensorFrame A U M N e' f') V) =
    DivisorClass.Chern.FramesFrame.Construction.frameTransitionUnit (sliceSectionFrame A U M e V)
      (sliceSectionFrame A U M e' V) *
    DivisorClass.Chern.FramesFrame.Construction.frameTransitionUnit (sliceSectionFrame A U N f V)
      (sliceSectionFrame A U N f' V) := by
  apply TensorFrames.Projective.frameTransitionUnit_of_product_coordinates _ _ _ _ _ _
    (fun m n => ((PresheafOfModules.sheafificationAdjunction
        (𝟙 (A.carrier.ringCatSheaf.over U).obj)).unit.app
        (PresheafOfModulesOfCommRing.Monoidal.tensorObj
          (R := (Over.forget U).op ⋙ A.carrier.presheaf) M.val N.val)).app
      (Opposite.op V) (m ⊗ₜ[Γ(A.carrier, V.left)] n))
  · exact localTensorFrame_unit_tmul A U M N e f V
  · exact localTensorFrame_unit_tmul A U M N e' f' V

end

end OAI.AlgebraicGeometry.SheafCohomology.TensorCoordinates.Projective
