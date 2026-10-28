import OAI.AlgebraicGeometry.Quotients.FiniteDescent.BinaryTensorApp
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections

/-! # Binary Tensor Of -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.BinaryTensorOf.Construction.BinaryTensorInvertibility

noncomputable section

/-! Tensor products detect invertibility of maps between trivialized line bundles. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections

universe u

variable {X : Scheme.{u}}

theorem unit (a b : End (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)) [IsIso (BinaryTensorId.Construction.BinaryTensorMap.map a b)] :
    IsIso a ∧ IsIso b := by
  have : IsIso (a ≫ b) := (BinaryTensorApp.Construction.BinaryTensorUnit.unit_conjugation a b) ▸ inferInstance
  have hu := (AbelianModuli.HilbertConstruction.Global.Sections.structureModuleEnd_isIso_iff (a ≫ b)).mp inferInstance
  change IsUnit (AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue X (b * a)) at hu
  rw [map_mul, (Commute.all _ _).isUnit_mul_iff] at hu
  exact ⟨(AbelianModuli.HilbertConstruction.Global.Sections.structureModuleEnd_isIso_iff a).mpr hu.2,
    (AbelianModuli.HilbertConstruction.Global.Sections.structureModuleEnd_isIso_iff b).mpr hu.1⟩

theorem of_frames {M M' N N' : X.Modules} (a : M ⟶ M') (b : N ⟶ N')
    (e : M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) (e' : M' ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)
    (h : N ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) (h' : N' ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)
    [IsIso (BinaryTensorId.Construction.BinaryTensorMap.map a b)] : IsIso a ∧ IsIso b := by
  let c : End (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) := e.inv ≫ a ≫ e'.hom
  let d : End (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) := h.inv ≫ b ≫ h'.hom
  have he : BinaryTensorId.Construction.BinaryTensorMap.map c d = BinaryTensorId.Construction.BinaryTensorMap.map e.inv h.inv ≫
      BinaryTensorId.Construction.BinaryTensorMap.map a b ≫ BinaryTensorId.Construction.BinaryTensorMap.map e'.hom h'.hom := by
    dsimp [c, d]
    rw [BinaryTensorId.Construction.BinaryTensorMap.map_comp, BinaryTensorId.Construction.BinaryTensorMap.map_comp]
  have : IsIso (BinaryTensorId.Construction.BinaryTensorMap.map c d) := he.symm ▸ inferInstance
  obtain ⟨hc, hd⟩ := unit c d
  have hc' : IsIso (e.inv ≫ a ≫ e'.hom) := hc
  have hd' : IsIso (h.inv ≫ b ≫ h'.hom) := hd
  exact ⟨(isIso_comp_left_iff _ _).mp ((isIso_comp_right_iff _ _).mp hc'),
    (isIso_comp_left_iff _ _).mp ((isIso_comp_right_iff _ _).mp hd')⟩

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.BinaryTensorOf.Construction.BinaryTensorInvertibility
