import OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.SourceCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.Ext
import OAI.NumberTheory.PadicHodge.IntegralComparison.Global.SectionCechEdge

/-! # Source Component -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.SourceComponent

noncomputable section

/-! The mixed Hom source edge becomes genuine global-section
restriction under the native free-frame Čech coordinates. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u z
variable {C : Type u} [Category.{0} C] [HasBinaryProducts C]
  {ι : Type} [Finite ι] (F : ι → C) (R : Type u) [CommRing R]
  (J : GrothendieckTopology C)
  [HasExt.{max u z} (Sheaf J (ModuleCat.{u} R))]
  (H : Sheaf J (ModuleCat.{u} R))

local notation "ε" => OAI.NumberTheory.PadicHodge.IntegralComparison.CoveringPresentationResolution.augmentation J R F
local notation "A" => Functor.obj (constantSheaf J (ModuleCat R)) (ModuleCat.of R R)

def restriction : (ExhaustiveSectionNaturality.globalSectionsFunctor R (ModuleCat.of R R)).obj H.obj ⟶
    (Differential.complex F R H.obj).X 0 :=
  Pi.lift (fun t : Fin 1 → ι => ModuleCat.ofHom
    { toFun := fun s => s.app (op (Presentation.TupleProducts.family F 0 t)) (1 : R)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl })

omit [Finite ι] [HasExt.{max u z} (Sheaf J (ModuleCat.{u} R))] in
theorem restriction_apply (b : (ExhaustiveSectionNaturality.globalSectionsFunctor R (ModuleCat.of R R)).obj H.obj)
    (t : Fin 1 → ι) :
    Differential.coordinate F R H.obj 0 t (restriction F R J H b) =
      b.app (op (Presentation.TupleProducts.family F 0 t)) (1 : R) :=
  ConcreteCategory.congr_hom (Pi.lift_comp_π _ t) b

omit [Finite ι] in
theorem coordinate (b : A ⟶ H) :
    (FrameCech.Ext.Comparison.comparison.{u,0,z} F R J H).hom.f 0
      (Abelian.Ext.mk₀ ((ε).f 0 ≫ b)) =
        ULift.up (restriction F R J H (IntegralComparison.Ext.ZeroPresheafSections.homLinearEquiv R J H b)) := by
  change ULift.up ((SectionIso.component F R J H 0).hom
    (Abelian.Ext.linearEquiv₀ (R := R) (Abelian.Ext.mk₀ ((ε).f 0 ≫ b)))) = _
  erw [Abelian.Ext.linearEquiv₀.apply_symm_apply]
  apply ULift.ext
  apply Module.ProductScalarKernel.element_ext
    (fun t : Fin 1 → ι => H.obj.obj (op (Presentation.TupleProducts.family F 0 t)))
  intro t
  exact (SectionIso.component_coordinate F R J H 0 ((ε).f 0 ≫ b) t).trans
    ((SourceCoordinates.coordinate F R J H b t).trans
      (restriction_apply F R J H (IntegralComparison.Ext.ZeroPresheafSections.homLinearEquiv R J H b) t).symm)

omit [Finite ι] in
theorem square :
    (IntegralComparison.Ext.ContravariantModuleFunctor.functor R H 0).map ((ε).f 0).op ≫
      (FrameCech.Ext.Comparison.comparison.{u,0,z} F R J H).hom.f 0 =
        (IntegralComparison.Ext.ZeroPresheafSections.iso.{u,0,u,z} R J).hom.app H ≫
          (ModuleCat.uliftFunctor.{z,u} R).map (restriction F R J H) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨b, rfl⟩ := (Abelian.Ext.mk₀_bijective A H).surjective x
  change (FrameCech.Ext.Comparison.comparison.{u,0,z} F R J H).hom.f 0
    ((Abelian.Ext.mk₀ ((ε).f 0)).comp (Abelian.Ext.mk₀ b) (Nat.zero_add 0)) = _
  erw [Abelian.Ext.mk₀_comp_mk₀, coordinate]
  exact congrArg (fun s => ULift.up (restriction F R J H s.down))
    (IntegralComparison.Ext.ZeroPresheafSections.equivalence_mk.{u,0,u,z} R J H b).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.SourceComponent
