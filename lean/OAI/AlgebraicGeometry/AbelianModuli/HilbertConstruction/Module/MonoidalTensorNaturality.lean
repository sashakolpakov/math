import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MonoidalTensorComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.MapSheafification

/-! # Monoidal Tensor Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MonoidalTensorNaturality

noncomputable section

/-! The comparison between the monoidal tensor and the actual sheaf tensor is natural in the first factor. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory
universe u

local instance traceNaturalityModulesMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules := SheafMonoidal.moduleMonoidalCategory X
local instance traceNaturalityPresheafMonoidal (X : Scheme.{u}) : MonoidalCategory X.PresheafOfModules :=
  PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
local instance traceNaturalitySheafificationLocalization (X : Scheme.{u}) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).IsLocalization
      (SheafificationLocalEquivalences.SheafTensorLocalization.sheafificationW (𝟙 X.ringCatSheaf.obj)) := SheafificationLocalEquivalences.SheafTensorLocalization.sheafificationW_isLocalization _
local instance traceNaturalitySheafificationMonoidal (X : Scheme.{u}) : (SheafificationLocalEquivalences.SheafTensorLocalization.sheafificationW (𝟙 X.ringCatSheaf.obj)).IsMonoidal :=
  SheafMonoidal.SheafTensorLocalization.instSheafificationW_isMonoidal_commRingSheaf X.sheaf.obj X.ringCatSheaf.property

theorem moduleMonoidalTensorIso_natural_left {X : Scheme.{u}} {M M' : X.Modules}
    (f : M ⟶ M') (N : X.Modules) :
    (f ▷ N) ≫ (MonoidalTensorComparison.moduleMonoidalTensorIso M' N).hom =
      (MonoidalTensorComparison.moduleMonoidalTensorIso M N).hom ≫ Tensor.Bifunctor.tensorModuleMap f (𝟙 N) := by
  let : MonoidalCategory (SheafOfModules X.ringCatSheaf) := SheafMonoidal.moduleMonoidalCategory X
  let F := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  have hc : f ≫ (MonoidalTensorComparison.moduleSheafifyValIso M').inv =
      (MonoidalTensorComparison.moduleSheafifyValIso M).inv ≫ F.map f.val :=
    (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit).inv.naturality f
  have hm : Tensor.Bifunctor.tensorModuleMap f (𝟙 N) = F.map (f.val ▷ N.val) := by
    rw [Tensor.MapSheafification.tensorModuleMap_eq_sheafification]
    apply congrArg F.map
    exact tensorHom_id f.val N.val
  rw [hm]
  let c : M ⟶ F.obj M.val := (MonoidalTensorComparison.moduleSheafifyValIso M).inv
  let c' : M' ⟶ F.obj M'.val := (MonoidalTensorComparison.moduleSheafifyValIso M').inv
  let d : N ⟶ F.obj N.val := (MonoidalTensorComparison.moduleSheafifyValIso N).inv
  let m : F.obj M.val ⊗ F.obj N.val ⟶ F.obj (M.val ⊗ N.val) :=
    (Localization.Monoidal.μ F (SheafificationLocalEquivalences.SheafTensorLocalization.sheafificationW (𝟙 X.ringCatSheaf.obj)) (Iso.refl _) M.val N.val).hom
  let m' : F.obj M'.val ⊗ F.obj N.val ⟶ F.obj (M'.val ⊗ N.val) :=
    (Localization.Monoidal.μ F (SheafificationLocalEquivalences.SheafTensorLocalization.sheafificationW (𝟙 X.ringCatSheaf.obj)) (Iso.refl _) M'.val N.val).hom
  have hμ : (F.map f.val ▷ F.obj N.val) ≫ m' = m ≫ F.map (f.val ▷ N.val) :=
    Localization.Monoidal.μ_natural_left F (SheafificationLocalEquivalences.SheafTensorLocalization.sheafificationW (𝟙 X.ringCatSheaf.obj))
      (Iso.refl _) f.val N.val
  exact (whiskerRight_comp_tensorHom_assoc f c' d m').trans
    ((congrArg (fun k => (k ⊗ₘ d) ≫ m') hc).trans
      ((tensorHom_comp_whiskerRight_assoc c (F.map f.val) d m').symm.trans
        (congrArg (fun k => (c ⊗ₘ d) ≫ k) hμ)))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MonoidalTensorNaturality
