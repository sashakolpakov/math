import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SectionFrameApps
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TensorSections
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

/-! # Tensor Section Frame -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorSectionFrame.Construction

noncomputable section

/-! A nonvanishing unit section trivializes a tensor factor, naturally in the other module. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory
open OAI.AlgebraicGeometry.SheafCohomology.Projective.TensorSections

universe u v

section Monoidal

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {P : C}

def tensorByUnitSection (M : C) (a : 𝟙_ C ⟶ P) : M ⟶ M ⊗ P :=
  (ρ_ M).inv ≫ (𝟙 M ⊗ₘ a)

theorem tensorByUnitSection_naturality {M N : C} (q : M ⟶ N) (a : 𝟙_ C ⟶ P) :
    q ≫ tensorByUnitSection N a = tensorByUnitSection M a ≫ (q ⊗ₘ 𝟙 P) := by
  unfold tensorByUnitSection
  rw [← Category.assoc, rightUnitor_inv_naturality, ← tensorHom_id,
    Category.assoc, tensor_id_comp_id_tensor, Category.assoc, id_tensor_comp_tensor_id]

theorem tensorByUnitSection_unit (a : 𝟙_ C ⟶ P) :
    tensorByUnitSection (𝟙_ C) a ≫ (λ_ P).hom = a := by
  rw [tensorByUnitSection, ← unitors_inv_equal, id_tensorHom]
  simpa only [Category.assoc] using (id_whiskerLeft_symm a).symm

end Monoidal

theorem moduleMap_over_isIso_iff {X : Scheme.{u}} {M N : X.Modules}
    (q : M ⟶ N) (U : X.Opens) :
    IsIso (q.over U) ↔ IsIso ((Scheme.Modules.pullback U.ι).map q) := by
  let F := (Scheme.Modules.overEquiv U).functor
  let e := Scheme.Modules.overFunctorEquiv U ≪≫ Scheme.Modules.restrictFunctorIsoPullback U.ι
  rw [← isIso_iff_of_reflects_iso (q.over U) F]
  have h : F.map (q.over U) ≫ (e.app N).hom =
      (e.app M).hom ≫ (Scheme.Modules.pullback U.ι).map q := e.hom.naturality q
  exact (isIso_comp_right_iff _ (e.app N).hom).symm.trans
    ((congrArg IsIso h).to_iff.trans (isIso_comp_left_iff (e.app M).hom _))

theorem moduleMap_app_isIso_of_pullback {X : Scheme.{u}} {M N : X.Modules}
    (q : M ⟶ N) (U : X.Opens) [IsIso ((Scheme.Modules.pullback U.ι).map q)] :
    IsIso (q.app U) := by
  have : IsIso (q.over U) := (moduleMap_over_isIso_iff q U).mpr inferInstance
  have hm : IsIso ((q.over U).val.app (.op (Over.mk (𝟙 U)))) :=
    (SheafOfModules.evaluation (X.ringCatSheaf.over U) (.op (Over.mk (𝟙 U)))).map_isIso (q.over U)
  exact @Functor.map_isIso _ _ _ _ _ _ (forget₂ (ModuleCat Γ(X, U)) AddCommGrpCat)
    (q.val.app (.op U)) hm

local instance tensorSectionFrameMonoidal (X : Scheme.{u}) :
    MonoidalCategory X.Modules := AlgebraicGeometry.SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory X

theorem tensorByUnitSection_pullback_isIso {X : Scheme.{u}} (M : X.Modules) {P : X.Modules}
    (a : 𝟙_ X.Modules ⟶ P) (U : X.Opens)
    [IsIso ((Scheme.Modules.pullback U.ι).map a)] :
    IsIso ((Scheme.Modules.pullback U.ι).map (tensorByUnitSection M a)) := by
  let F := Scheme.Modules.pullback U.ι
  let : F.Monoidal := AlgebraicGeometry.SheafCohomology.Projective.PullbackTensorGeneral.Scheme.Modules.pullbackMonoidal U.ι
  change IsIso (F.map ((ρ_ M).inv ≫ (𝟙 M ⊗ₘ a)))
  rw [Functor.map_comp, Functor.Monoidal.map_tensor, F.map_id]
  infer_instance

def tensorSectionFrameAppEquiv {X : Scheme.{u}} (M : X.Modules) {P : X.Modules}
    (a : 𝟙_ X.Modules ⟶ P) (U : X.Opens)
    [IsIso ((Scheme.Modules.pullback U.ι).map a)] :
    Γ(M, U) ≃ₗ[Γ(X, U)] Γ(M ⊗ P, U) := by
  have := tensorByUnitSection_pullback_isIso M a U
  have := moduleMap_app_isIso_of_pullback (tensorByUnitSection M a) U
  exact LinearEquiv.ofBijective ((tensorByUnitSection M a).val.app (.op U)).hom
    (ConcreteCategory.bijective_of_isIso ((tensorByUnitSection M a).app U))

theorem tensorSectionFrameAppEquiv_naturality
    {X : Scheme.{u}} {M N P : X.Modules} (q : M ⟶ N)
    (a : 𝟙_ X.Modules ⟶ P) (U : X.Opens)
    [IsIso ((Scheme.Modules.pullback U.ι).map a)] (x : Γ(M ⊗ P, U)) :
    (tensorSectionFrameAppEquiv N a U).symm ((q ⊗ₘ 𝟙 P).app U x) =
      q.app U ((tensorSectionFrameAppEquiv M a U).symm x) := by
  apply (tensorSectionFrameAppEquiv N a U).injective
  rw [LinearEquiv.apply_symm_apply]
  have h := congrArg (fun z : M ⟶ N ⊗ P =>
    z.app U ((tensorSectionFrameAppEquiv M a U).symm x)) (tensorByUnitSection_naturality q a)
  have he : (tensorByUnitSection M a).app U ((tensorSectionFrameAppEquiv M a U).symm x) = x :=
    (tensorSectionFrameAppEquiv M a U).apply_symm_apply x
  change (tensorByUnitSection N a).app U (q.app U ((tensorSectionFrameAppEquiv M a U).symm x)) =
    (q ⊗ₘ 𝟙 P).app U ((tensorByUnitSection M a).app U ((tensorSectionFrameAppEquiv M a U).symm x)) at h
  rw [he] at h
  exact h.symm

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorSectionFrame.Construction
