import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorUnitCoefficient
import OAI.AlgebraicGeometry.SheafCohomology.Projective.SheafificationTensorAssociator
import OAI.AlgebraicGeometry.SheafCohomology.Projective.PowerCancellationPairing

/-! # Local Tensor Unit -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LocalTensorUnit.Construction

noncomputable section

/-! The tensor unit and multiplication by a section, evaluated on arbitrary local sections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory Opposite
open scoped TensorProduct

universe u

local instance localTensorUnitMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  AlgebraicGeometry.SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory X
local instance localTensorUnitSheafMonoidal (X : Scheme.{u}) :
    MonoidalCategory (SheafOfModules X.ringCatSheaf) := AlgebraicGeometry.SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory X
local instance localTensorUnitLocalization (X : Scheme.{u}) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).IsLocalization
      (AlgebraicGeometry.SheafCohomology.Projective.OfModulesMonoidal.PresheafOfModules.sheafificationW (𝟙 X.ringCatSheaf.obj)) :=
  AlgebraicGeometry.SheafCohomology.Projective.OfModulesMonoidal.PresheafOfModules.sheafificationW_isLocalization X.ringCatSheaf
local instance localTensorUnitWMonoidal (X : Scheme.{u}) :
    (AlgebraicGeometry.SheafCohomology.Projective.OfModulesMonoidal.PresheafOfModules.sheafificationW (𝟙 X.ringCatSheaf.obj)).IsMonoidal := by
  change (AlgebraicGeometry.SheafCohomology.Projective.OfModulesMonoidal.PresheafOfModules.sheafificationW
    (𝟙 (⟨X.sheaf.obj ⋙ forget₂ CommRingCat RingCat,
      X.ringCatSheaf.property⟩ : TopCat.Sheaf RingCat X).obj)).IsMonoidal
  infer_instance
local instance localTensorUnitSheafificationMonoidal (X : Scheme.{u}) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).Monoidal :=
  inferInstanceAs ((Localization.Monoidal.toMonoidalCategory
    (L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
    (W := AlgebraicGeometry.SheafCohomology.Projective.OfModulesMonoidal.PresheafOfModules.sheafificationW (𝟙 X.ringCatSheaf.obj))
    (Iso.refl _)).Monoidal)

theorem sheafificationUnit_localMonoidalUnitSection (X : Scheme.{u}) (U : X.Opens) :
    (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
      (𝟙_ X.PresheafOfModules)).app (op U)) (show Γ(X, U) from 1) =
        AlgebraicGeometry.SheafCohomology.Projective.PowerCancellationPairing.localMonoidalUnitSection X U :=
  (AlgebraicGeometry.SheafCohomology.Projective.PullbackTensorGeneral.Scheme.Modules.sheafifyValIso_inv_app_apply (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X) U (show Γ(X, U) from 1)).symm

theorem sheafification_rightUnitor_local_tensor {X : Scheme.{u}}
    (A : X.PresheafOfModules) (U : X.Opens) (x : A.obj (op U)) :
    let L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
    let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
    (ρ_ (L.obj A)).hom.val.app (op U)
      (AlgebraicGeometry.SheafCohomology.Projective.TensorSections.tensorSection (L.obj A) (𝟙_ X.Modules) U
        ((adj.unit.app A).app (op U) x) (AlgebraicGeometry.SheafCohomology.Projective.PowerCancellationPairing.localMonoidalUnitSection X U)) =
      (adj.unit.app A).app (op U) x := by
  let L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  let O := 𝟙_ X.PresheafOfModules
  let z : (A ⊗ O).obj (op U) := x ⊗ₜ (show Γ(X, U) from 1)
  have hu := Functor.OplaxMonoidal.right_unitality_hom L A
  have hη : Functor.OplaxMonoidal.η L = 𝟙 _ := rfl
  erw [hη, whiskerLeft_id, Category.id_comp] at hu
  have he := congrArg (fun q => q.val.app (op U) ((adj.unit.app (A ⊗ O)).app (op U) z)) hu
  change (ρ_ (L.obj A)).hom.val.app (op U)
      ((Functor.OplaxMonoidal.δ L A O).val.app (op U)
        ((adj.unit.app (A ⊗ O)).app (op U) z)) =
      (L.map (ρ_ A).hom).val.app (op U) ((adj.unit.app (A ⊗ O)).app (op U) z) at he
  have ht := AlgebraicGeometry.SheafCohomology.Projective.TensorSections.sheafification_δ_unit_tmul_eq_tensorSection A O U x (show Γ(X, U) from 1)
  have ho : (adj.unit.app O).app (op U) (show Γ(X, U) from 1) =
      AlgebraicGeometry.SheafCohomology.Projective.PowerCancellationPairing.localMonoidalUnitSection X U := sheafificationUnit_localMonoidalUnitSection X U
  have ht' : (Functor.OplaxMonoidal.δ L A O).val.app (op U)
      ((adj.unit.app (A ⊗ O)).app (op U) z) =
      AlgebraicGeometry.SheafCohomology.Projective.TensorSections.tensorSection (L.obj A) (𝟙_ X.Modules) U ((adj.unit.app A).app (op U) x)
        (AlgebraicGeometry.SheafCohomology.Projective.PowerCancellationPairing.localMonoidalUnitSection X U) := ht.trans
    (congrArg (fun y => AlgebraicGeometry.SheafCohomology.Projective.TensorSections.tensorSection (L.obj A) (𝟙_ X.Modules) U
      ((adj.unit.app A).app (op U) x) y) ho)
  rw [ht'] at he
  have hn := congrArg (fun q => q.app (op U) z) (adj.unit.naturality (ρ_ A).hom)
  have hx : (ρ_ A).hom.app (op U) z = x := by
    let AA : ModuleCat (X.sheaf.obj.obj (op U)) := A.obj (op U)
    have hh := ModuleCat.MonoidalCategory.rightUnitor_hom_apply
      (R := X.sheaf.obj.obj (op U)) (M := AA) x (1 : X.sheaf.obj.obj (op U))
    exact hh.trans (one_smul _ _)
  change (adj.unit.app A).app (op U) ((ρ_ A).hom.app (op U) z) =
    (L.map (ρ_ A).hom).val.app (op U) ((adj.unit.app (A ⊗ O)).app (op U) z) at hn
  rw [hx] at hn
  exact he.trans hn.symm

theorem rightUnitor_naturality_app {X : Scheme.{u}} {M N : X.Modules}
    (q : M ⟶ N) (U : X.Opens) (y : Γ(M ⊗ 𝟙_ X.Modules, U)) :
    (ρ_ N).hom.val.app (op U) ((q ⊗ₘ 𝟙 (𝟙_ X.Modules)).val.app (op U) y) =
      q.val.app (op U) ((ρ_ M).hom.val.app (op U) y) := by
  have h : (q ⊗ₘ 𝟙 (𝟙_ X.Modules)) ≫ (ρ_ N).hom = (ρ_ M).hom ≫ q := by
    rw [tensorHom_id]
    exact rightUnitor_naturality q
  exact congrArg (fun f : M ⊗ 𝟙_ X.Modules ⟶ N => f.val.app (op U) y) h

theorem rightUnitor_local_tensorSection {X : Scheme.{u}} (M : X.Modules)
    (U : X.Opens) (x : Γ(M, U)) :
    (ρ_ M).hom.val.app (op U)
      (AlgebraicGeometry.SheafCohomology.Projective.TensorSections.tensorSection M (𝟙_ X.Modules) U x (AlgebraicGeometry.SheafCohomology.Projective.PowerCancellationPairing.localMonoidalUnitSection X U)) = x := by
  let L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  let c := AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.sheafifyValIso M
  let y := AlgebraicGeometry.SheafCohomology.Projective.TensorSections.tensorSection (L.obj M.val) (𝟙_ X.Modules) U
    ((adj.unit.app M.val).app (op U) x) (AlgebraicGeometry.SheafCohomology.Projective.PowerCancellationPairing.localMonoidalUnitSection X U)
  have h := rightUnitor_naturality_app c.hom U y
  have ht := AlgebraicGeometry.SheafCohomology.Projective.TensorFrameSections.tensorSection_map c.hom (𝟙 (𝟙_ X.Modules)) U
    ((adj.unit.app M.val).app (op U) x) (AlgebraicGeometry.SheafCohomology.Projective.PowerCancellationPairing.localMonoidalUnitSection X U)
  have ht' : (c.hom ⊗ₘ 𝟙 (𝟙_ X.Modules)).val.app (op U) y =
      AlgebraicGeometry.SheafCohomology.Projective.TensorSections.tensorSection M (𝟙_ X.Modules) U x (AlgebraicGeometry.SheafCohomology.Projective.PowerCancellationPairing.localMonoidalUnitSection X U) :=
    ht.trans (congrArg (fun z => AlgebraicGeometry.SheafCohomology.Projective.TensorSections.tensorSection M (𝟙_ X.Modules) U z
      (AlgebraicGeometry.SheafCohomology.Projective.PowerCancellationPairing.localMonoidalUnitSection X U)) (AlgebraicGeometry.SheafCohomology.Projective.TensorFrameSections.sheafifyValIso_hom_unit_apply M U x))
  have hr := sheafification_rightUnitor_local_tensor M.val U x
  exact (congrArg ((ρ_ M).hom.val.app (op U)) ht').symm.trans
    (h.trans ((congrArg (c.hom.val.app (op U)) hr).trans (AlgebraicGeometry.SheafCohomology.Projective.TensorFrameSections.sheafifyValIso_hom_unit_apply M U x)))

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LocalTensorUnit.Construction
