import OAI.AlgebraicGeometry.SheafCohomology.Projective.TensorSectionBilinear
import OAI.AlgebraicGeometry.SheafCohomology.Projective.SectionIdentities
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TensorFrameSections

/-! # Tensor Conjugated Map Sections -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.TensorConjugatedMapSections

noncomputable section

/-! A map transported through tensor cancellation preserves its local scalar coefficient. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory Opposite
universe u
local instance tensorConjugatedMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Monoidal.Scheme.Modules.monoidalCategory X

def tensorConjugatedMap {X : Scheme.{u}} {A B T P Q : X.Modules}
    (e : A ⊗ T ≅ P) (d : B ⊗ T ≅ Q) (f : A ⟶ B) : P ⟶ Q :=
  e.inv ≫ (f ⊗ₘ 𝟙 T) ≫ d.hom

theorem tensorConjugatedMap_apply_hom {X : Scheme.{u}} {A B T P Q : X.Modules}
    (e : A ⊗ T ≅ P) (d : B ⊗ T ≅ Q) (f : A ⟶ B) (U : X.Opens)
    (x : Γ(A ⊗ T, U)) :
    (tensorConjugatedMap e d f).val.app (op U) (e.hom.val.app (op U) x) =
      d.hom.val.app (op U) ((f ⊗ₘ 𝟙 T).val.app (op U) x) := by
  unfold tensorConjugatedMap
  erw [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
    SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
    SectionIdentities.Scheme.Modules.iso_inv_hom_app_applyT e.symm]

theorem tensorConjugatedMap_section {X : Scheme.{u}} {A B T P Q : X.Modules}
    (e : A ⊗ T ≅ P) (d : B ⊗ T ≅ Q) (f : A ⟶ B) (U : X.Opens)
    (a : Γ(A, U)) (b : Γ(B, U)) (t : Γ(T, U))
    (p : Γ(P, U)) (q : Γ(Q, U)) (c : Γ(X, U))
    (he : e.hom.val.app (op U) (TensorSections.tensorSection A T U a t) = p)
    (hd : d.hom.val.app (op U) (TensorSections.tensorSection B T U b t) = q)
    (hf : f.val.app (op U) a = c • b) :
    (tensorConjugatedMap e d f).val.app (op U) p = c • q := by
  unfold tensorConjugatedMap
  erw [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
    SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  erw [← he, SectionIdentities.Scheme.Modules.iso_inv_hom_app_applyT e.symm, TensorFrameSections.tensorSection_map]
  change d.hom.val.app (op U) (TensorSections.tensorSection B T U (f.val.app (op U) a) t) = _
  rw [hf, TensorSectionBilinear.tensorSection_smul_left, map_smul, hd]

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.TensorConjugatedMapSections
