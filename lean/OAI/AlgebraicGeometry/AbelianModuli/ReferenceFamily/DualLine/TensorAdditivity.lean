import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedDual.TensorFrames
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualLine.FrameIndependence
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pullback.TensorTransition
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.UnitCechProducts
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.TensorCechCoefficients

/-! # Tensor Additivity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualLine.TensorAdditivity

noncomputable section

section

/-! On any common normalized affine atlas, the original tensor
line bundle has the sum of the two algebraic deformation classes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open _root_.CategoryTheory.MonoidalCategory OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FramedHom

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType X.hom] [IsReduced X.left]
    [IsAffineHom (pullback.diagonal (terminal.from (LieRanks.dualNumberTest ℂ ⊗ X).left))]
    (L K : HilbertConstruction.Line.Bundles.LineBundle (LieRanks.dualNumberTest ℂ ⊗ X).left)
    (e₀ : (Scheme.Modules.pullback (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left).obj L.sheaf ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X.left)
    (d₀ : (Scheme.Modules.pullback (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left).obj K.sheaf ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X.left)

theorem normalizedDualTensorClassOn {I : Type} (U : I → (LieRanks.dualNumberTest ℂ ⊗ X).left.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hcover : iSup (Dual.CechCoefficient.dualReducedCechCover X U) = ⊤)
    (e : ∀ i, (Scheme.Modules.pullback (U i).ι).obj L.sheaf ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule (U i).toScheme)
    (d : ∀ i, (Scheme.Modules.pullback (U i).ι).obj K.sheaf ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule (U i).toScheme)
    (he : ∀ i, Isogenies.NeighborCounting.FramedHom.pullbackFrame (DualOpen.Product.dualOpenReduction X (U i)) (e i) = Dual.NormalizedLocalFrames.prescribedReducedLocalFrame X e₀ (U i))
    (hd : ∀ i, Isogenies.NeighborCounting.FramedHom.pullbackFrame (DualOpen.Product.dualOpenReduction X (U i)) (d i) = Dual.NormalizedLocalFrames.prescribedReducedLocalFrame X d₀ (U i)) :
    DeformationClass.normalizedDualFrameClass X (L.tensor K) (NormalizedDual.TensorFrames.dualTensorReductionFrame X L K e₀ d₀)
      (fun i => NormalizedDual.TensorFrames.normalizedDualTensorFrameOn X L K e₀ d₀ (U i) (hU i) (e i) (d i) (he i) (hd i)) hcover =
    DeformationClass.normalizedDualFrameClass X L e₀ (fun i => ⟨U i, hU i, e i, he i⟩) hcover +
      DeformationClass.normalizedDualFrameClass X K d₀ (fun i => ⟨U i, hU i, d i, hd i⟩) hcover := by
  let s (i : I) : Dual.NormalizedFrameCover.NormalizedDualFrame X L e₀ := ⟨U i, hU i, e i, he i⟩
  let t (i : I) : Dual.NormalizedFrameCover.NormalizedDualFrame X K d₀ := ⟨U i, hU i, d i, hd i⟩
  let v (i : I) := NormalizedDual.TensorFrames.normalizedDualTensorFrameOn X L K e₀ d₀ (U i) (hU i) (e i) (d i) (he i) (hd i)
  refine Dual.UnitCechProducts.dualUnitCechClass_product X.left.sheaf (Dual.CechCoefficient.dualReducedCechCover X U) hcover
    (LineFrameDualCech.lineFrameDualCech X (fun i => (s i).localFrame X L e₀) hU)
    (LineFrameDualCech.lineFrameDualCech X (fun i => (t i).localFrame X K d₀) hU)
    (LineFrameDualCech.lineFrameDualCech X (fun i => (v i).localFrame X (L.tensor K) (NormalizedDual.TensorFrames.dualTensorReductionFrame X L K e₀ d₀)) hU)
    (NormalizedDual.Cech.normalizedDualFrames_cech X L e₀ s) (NormalizedDual.Cech.normalizedDualFrames_cech X K d₀ t)
    (NormalizedDual.Cech.normalizedDualFrames_cech X (L.tensor K) (NormalizedDual.TensorFrames.dualTensorReductionFrame X L K e₀ d₀) v)
    (LineFrameDualCech.lineFrameDualCech_cocycle X (fun i => (s i).localFrame X L e₀) hU)
    (LineFrameDualCech.lineFrameDualCech_cocycle X (fun i => (t i).localFrame X K d₀) hU)
    (LineFrameDualCech.lineFrameDualCech_cocycle X (fun i => (v i).localFrame X (L.tensor K) (NormalizedDual.TensorFrames.dualTensorReductionFrame X L K e₀ d₀)) hU) ?_
  intro a
  exact Dual.TensorCechCoefficients.lineFrameDualCech_tensor X L.sheaf K.sheaf U hU e d a

end

/-! Tensor products add the intrinsic algebraic deformation classes.
The simultaneous normalized affine atlas is constructed from the two
actual line bundles and their prescribed reduced trivializations. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open _root_.CategoryTheory.MonoidalCategory

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType X.hom] [IsReduced X.left]
    [IsAffineHom (pullback.diagonal (terminal.from (LieRanks.dualNumberTest ℂ ⊗ X).left))]
    (L K : HilbertConstruction.Line.Bundles.LineBundle (LieRanks.dualNumberTest ℂ ⊗ X).left)
    (e₀ : (Scheme.Modules.pullback (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left).obj L.sheaf ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X.left)
    (d₀ : (Scheme.Modules.pullback (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left).obj K.sheaf ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X.left)

theorem dualLineDeformationClass_tensor :
    DeformationClass.dualLineDeformationClass X (L.tensor K) (NormalizedDual.TensorFrames.dualTensorReductionFrame X L K e₀ d₀) =
      DeformationClass.dualLineDeformationClass X L e₀ + DeformationClass.dualLineDeformationClass X K d₀ := by
  let a := Dual.NormalizedFrameCover.normalizedDualFrameAt X L e₀
  let b := Dual.NormalizedFrameCover.normalizedDualFrameAt X K d₀
  let U (i : X.left) := (a i).domain ⊓ (b i).domain
  have hU (i : X.left) : IsAffineOpen (U i) := (a i).affine.inf (b i).affine
  let s (i : X.left) := (a i).restrict X L e₀ (U i) (hU i) inf_le_left
  let t (i : X.left) := (b i).restrict X K d₀ (U i) (hU i) inf_le_right
  have hcover : iSup (Dual.CechCoefficient.dualReducedCechCover X U) = ⊤ := by
    apply top_unique
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, Dual.NormalizedFrameCover.normalizedDualFrameAt_mem X L e₀ x, Dual.NormalizedFrameCover.normalizedDualFrameAt_mem X K d₀ x⟩
  let v (i : X.left) := NormalizedDual.TensorFrames.normalizedDualTensorFrameOn X L K e₀ d₀ (U i) (hU i)
    (s i).frame (t i).frame (s i).reduces (t i).reduces
  have h := normalizedDualTensorClassOn X L K e₀ d₀ U hU hcover
    (fun i => (s i).frame) (fun i => (t i).frame) (fun i => (s i).reduces) (fun i => (t i).reduces)
  have he := FrameIndependence.dualLineDeformationClass_eq_frames X L e₀ s hcover
  have hd := FrameIndependence.dualLineDeformationClass_eq_frames X K d₀ t hcover
  exact (FrameIndependence.dualLineDeformationClass_eq_frames X (L.tensor K) (NormalizedDual.TensorFrames.dualTensorReductionFrame X L K e₀ d₀) v hcover).trans
    (h.trans (congrArg₂ (· + ·) he hd).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualLine.TensorAdditivity
