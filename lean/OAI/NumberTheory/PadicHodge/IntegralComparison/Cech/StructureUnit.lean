import OAI.NumberTheory.PadicHodge.IntegralComparison.Global.StructureUnit
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ZeroSections

/-! # Structure Unit -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.StructureUnit

noncomputable section

/-! The constant-function map identifies the coefficient ring with
the degree-zero Čech cohomology of the direct image of the structure
sheaf whenever global functions are constant. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Scheme.Modules

universe u

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (π : Y ⟶ S)
  {ι : Type u} [LinearOrder ι] (U : ι → Y.Opens) (hU : iSup U = ⊤)

abbrev cohomology :=
  (AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π (Global.StructureUnit.directImage f) U).homology 0

def unit : cohomology f π U :=
  (ZeroSections.iso π U hU (Global.StructureUnit.directImage f)).hom
    (show (OrderedCech.Augmentation.sections π).obj (Global.StructureUnit.directImage f)
      from (1 : Γ(X, ⊤)))

def map : ModuleCat.of Γ(S, ⊤) Γ(S, ⊤) ⟶ cohomology f π U :=
  Global.StructureUnit.map f π ≫
    (ZeroSections.iso π U hU (Global.StructureUnit.directImage f)).hom

@[simp]
theorem map_one : map f π U hU 1 = unit f π U hU := by
  change (ZeroSections.iso π U hU (Global.StructureUnit.directImage f)).hom
    (Global.StructureUnit.map f π 1) = _
  rw [Global.StructureUnit.map_one]
  rfl

instance map_isIso [IsIso (f ≫ π).appTop] : IsIso (map f π U hU) := by
  unfold map
  infer_instance

def iso [IsIso (f ≫ π).appTop] : ModuleCat.of Γ(S, ⊤) Γ(S, ⊤) ≅ cohomology f π U :=
  asIso (map f π U hU)

@[simp]
theorem iso_one [IsIso (f ≫ π).appTop] : (iso f π U hU).toLinearEquiv 1 = unit f π U hU :=
  map_one f π U hU

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.StructureUnit
