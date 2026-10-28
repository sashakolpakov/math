import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MonoidalTensorNaturality

/-! # Monoidal Tensor Right Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MonoidalTensorRightNaturality

noncomputable section

/-! The monoidal-to-actual tensor comparison is natural in the second factor. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory
universe u

local instance e33RightTensorNaturalityModulesMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules := SheafMonoidal.moduleMonoidalCategory X
local instance e33RightTensorNaturalityPresheafMonoidal (X : Scheme.{u}) : MonoidalCategory X.PresheafOfModules :=
  PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
local instance e33RightTensorNaturalitySheafificationLocalization (X : Scheme.{u}) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).IsLocalization
      (SheafificationLocalEquivalences.SheafTensorLocalization.sheafificationW (𝟙 X.ringCatSheaf.obj)) := SheafificationLocalEquivalences.SheafTensorLocalization.sheafificationW_isLocalization _
local instance e33RightTensorNaturalitySheafificationMonoidal (X : Scheme.{u}) : (SheafificationLocalEquivalences.SheafTensorLocalization.sheafificationW (𝟙 X.ringCatSheaf.obj)).IsMonoidal :=
  SheafMonoidal.SheafTensorLocalization.instSheafificationW_isMonoidal_commRingSheaf X.sheaf.obj X.ringCatSheaf.property

theorem moduleMonoidalTensorIso_natural_right {X : Scheme.{u}} (M : X.Modules)
    {N N' : X.Modules} (f : N ⟶ N') :
    (M ◁ f) ≫ (MonoidalTensorComparison.moduleMonoidalTensorIso M N').hom =
      (MonoidalTensorComparison.moduleMonoidalTensorIso M N).hom ≫ Tensor.Bifunctor.tensorModuleMap (𝟙 M) f := by
  let : MonoidalCategory (SheafOfModules X.ringCatSheaf) := SheafMonoidal.moduleMonoidalCategory X
  let F := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  have hc : f ≫ (MonoidalTensorComparison.moduleSheafifyValIso N').inv =
      (MonoidalTensorComparison.moduleSheafifyValIso N).inv ≫ F.map f.val :=
    (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit).inv.naturality f
  have hm : Tensor.Bifunctor.tensorModuleMap (𝟙 M) f = F.map (M.val ◁ f.val) := by
    rw [Tensor.MapSheafification.tensorModuleMap_eq_sheafification]
    apply congrArg F.map
    exact id_tensorHom M.val f.val
  rw [hm]
  let c : M ⟶ F.obj M.val := (MonoidalTensorComparison.moduleSheafifyValIso M).inv
  let d : N ⟶ F.obj N.val := (MonoidalTensorComparison.moduleSheafifyValIso N).inv
  let d' : N' ⟶ F.obj N'.val := (MonoidalTensorComparison.moduleSheafifyValIso N').inv
  let m : F.obj M.val ⊗ F.obj N.val ⟶ F.obj (M.val ⊗ N.val) :=
    (Localization.Monoidal.μ F (SheafificationLocalEquivalences.SheafTensorLocalization.sheafificationW (𝟙 X.ringCatSheaf.obj)) (Iso.refl _) M.val N.val).hom
  let m' : F.obj M.val ⊗ F.obj N'.val ⟶ F.obj (M.val ⊗ N'.val) :=
    (Localization.Monoidal.μ F (SheafificationLocalEquivalences.SheafTensorLocalization.sheafificationW (𝟙 X.ringCatSheaf.obj)) (Iso.refl _) M.val N'.val).hom
  have hμ : (F.obj M.val ◁ F.map f.val) ≫ m' = m ≫ F.map (M.val ◁ f.val) :=
    Localization.Monoidal.μ_natural_right F (SheafificationLocalEquivalences.SheafTensorLocalization.sheafificationW (𝟙 X.ringCatSheaf.obj))
      (Iso.refl _) M.val f.val
  exact (whiskerLeft_comp_tensorHom_assoc c f d' m').trans
    ((congrArg (fun k => (c ⊗ₘ k) ≫ m') hc).trans
      ((tensorHom_comp_whiskerLeft_assoc c d (F.map f.val) m').symm.trans
        (congrArg (fun k => (c ⊗ₘ d) ≫ k) hμ)))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MonoidalTensorRightNaturality
