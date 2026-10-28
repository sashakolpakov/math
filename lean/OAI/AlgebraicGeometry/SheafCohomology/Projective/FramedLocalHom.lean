import OAI.AlgebraicGeometry.SheafCohomology.Projective.OverGeneratorRestriction
import OAI.AlgebraicGeometry.SheafCohomology.Projective.FrameSections

/-! # Framed Local Hom -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.FramedLocalHom

noncomputable section

/-! Local module maps defined by a rank-one frame and a target section. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
universe u

def framedLocalHom {X : Scheme.{u}} (L M : X.Modules) (U : X.Opens)
    (e : L.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    (s : Γ(M, U)) : L.over U ⟶ M.over U := e.hom ≫ OverGenerator.overGeneratorHom M U s

theorem linearHomRestrict_frame {X : Scheme.{u}} (L : X.Modules)
    {U V : X.Opens} (h : V ≤ U)
    (e : L.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) :
    LinearHom.linearHomRestrict X.ringCatSheaf L (Invertible.Scheme.Modules.unitObj X)
      (homOfLE h).op e.hom =
    (Dual.SheafOfModules.restrictOverTrivialization X.ringCatSheaf L U e
      (Over.mk (homOfLE h))).hom := by
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro Z
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

theorem framedLocalHom_restrict {X : Scheme.{u}} (L M : X.Modules)
    {U V : X.Opens} (h : V ≤ U)
    (e : L.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    (s : Γ(M, U)) :
    LinearHom.linearHomRestrict X.ringCatSheaf L M (homOfLE h).op (framedLocalHom L M U e s) =
    framedLocalHom L M V
      (Dual.SheafOfModules.restrictOverTrivialization X.ringCatSheaf L U e
        (Over.mk (homOfLE h))) (M.presheaf.map (homOfLE h).op s) := by
  unfold framedLocalHom
  rw [OverGeneratorRestriction.linearHomRestrict_comp L (Invertible.Scheme.Modules.unitObj X) M,
    linearHomRestrict_frame, OverGeneratorRestriction.linearHomRestrict_overGeneratorHom]

theorem framedLocalHom_eq_of_transition {X : Scheme.{u}} (L M : X.Modules)
    (U : X.Opens)
    (e g : L.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    (r : Γ(X, U)) (s t : Γ(M, U))
    (hg : g.hom = e.hom ≫ Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U r)
    (hs : s = r • t) :
    framedLocalHom L M U e s = framedLocalHom L M U g t := by
  unfold framedLocalHom
  rw [hg, Category.assoc, OverGeneratorRestriction.overUnitScalarEnd_comp_overGeneratorHom, hs]

theorem framedLocalHom_apply_frame {X : Scheme.{u}} (L M : X.Modules)
    (U : X.Opens)
    (e : L.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    (s : Γ(M, U)) :
    (framedLocalHom L M U e s).val.app (.op (Over.mk (𝟙 U)))
      (FrameSections.overTrivializationSection L U e 1) = s := by
  have he0 := congrArg (fun f => f.val.app (.op (Over.mk (𝟙 U)))) e.inv_hom_id
  let oneU : (_root_.SheafOfModules.unit (X.ringCatSheaf.over U)).val.obj
      (.op (Over.mk (𝟙 U))) := (show Γ(X, U) from 1)
  have he := ConcreteCategory.congr_hom he0 oneU
  change e.hom.val.app (.op (Over.mk (𝟙 U)))
    (FrameSections.overTrivializationSection L U e 1) = (show Γ(X, U) from 1) at he
  change (OverGenerator.overGeneratorHom M U s).val.app (.op (Over.mk (𝟙 U)))
    (e.hom.val.app (.op (Over.mk (𝟙 U))) (FrameSections.overTrivializationSection L U e 1)) = s
  rw [he, OverGenerator.overGeneratorHom_app]
  change (1 : Γ(X, U)) • M.presheaf.map (𝟙 (.op U)) s = s
  rw [M.presheaf.map_id, ConcreteCategory.id_apply, one_smul]

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.FramedLocalHom
