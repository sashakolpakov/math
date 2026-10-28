import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PresheafModuleBasisMaps
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.PowerSheaf

/-! # Basis Sheafification Maps -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A compatible basis map from a module presheaf to a sheaf induces an actual map from its sheafification, with the prescribed values after the unit. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u v

variable {X : Scheme.{u}} {ι : Type v} {B : ι → X.Opens} {P : X.PresheafOfModules} {N : X.Modules}
variable (D : PresheafModuleBasisMaps.PresheafModuleBasisMap B P N) (hB : Opens.IsBasis (Set.range B))

def PresheafModuleBasisMaps.PresheafModuleBasisMap.sheafificationMap : (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P ⟶ N :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv P N).symm (D.extend hB)

theorem PresheafModuleBasisMaps.PresheafModuleBasisMap.sheafificationMap_unit :
    (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P ≫
      (SheafOfModules.forget X.ringCatSheaf ⋙ PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
        (D.sheafificationMap hB) = D.extend hB := by
  exact (Adjunction.homEquiv_unit _ P N (D.sheafificationMap hB)).symm.trans
    (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv P N).apply_symm_apply (D.extend hB))

theorem PresheafModuleBasisMaps.PresheafModuleBasisMap.sheafificationMap_unit_app (i : ι) (x : P.obj (.op (B i))) :
    (D.sheafificationMap hB).val.app (.op (B i))
      (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P).app (.op (B i)) x) =
      D.app i x :=
  (congrArg (fun f => f.app (.op (B i)) x) (D.sheafificationMap_unit hB)).trans (D.extend_app hB i x)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
