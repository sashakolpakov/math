import OAI.AlgebraicGeometry.SheafCohomology.Projective.ZeroCyclesLinearSections
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechFunctor

/-! # Augmentation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.Augmentation

noncomputable section

/-! The actual global-section augmentation of the ordered base-linear
Čech complex, including exactness and naturality. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false

open OAI.AlgebraicGeometry.SheafCohomology.Projective.ZeroCyclesLinearSections Scheme.Modules

universe u

variable {X S : Scheme.{u}} (π : X ⟶ S)

def sections : X.Modules ⥤ ModuleCat.{u} Γ(S, ⊤) :=
  SheafOfModules.evaluation X.ringCatSheaf (op ⊤) ⋙ ModuleCat.restrictScalars π.appTop.hom

instance sections_additive : (sections π).Additive where
  map_add := rfl

variable {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)

def map (M : X.Modules) : (sections π).obj M ⟶ (AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U).X 0 :=
  Limits.Pi.lift (fun a : AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 0 =>
    ModuleCat.ofHom (X := (sections π).obj M) (Y := AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U 0 a.val)
      (AlgebraicGeometry.SheafCohomology.Projective.BaseGlobalRestriction.baseGlobalRestriction π M (∏ᶜ fun k : Fin 1 => U (a.val k))))

@[reassoc]
theorem map_π (M : X.Modules) (a : AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 0) :
    Augmentation.map π U M ≫ Pi.π (fun b : AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 0 => AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U 0 b.val) a =
      ModuleCat.ofHom (X := (sections π).obj M) (Y := AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U 0 a.val)
        (AlgebraicGeometry.SheafCohomology.Projective.BaseGlobalRestriction.baseGlobalRestriction π M (∏ᶜ fun k : Fin 1 => U (a.val k))) :=
  Pi.lift_comp_π _ _

theorem map_eq_zeroCycle (M : X.Modules) (hU : iSup U = ⊤) (x : (sections π).obj M) :
    Augmentation.map π U M x = (AlgebraicGeometry.SheafCohomology.Projective.ZeroCyclesLinearSections.orderedBaseTopSectionsZeroCyclesLinearEquiv π M U hU x).val := by
  apply AlgebraicGeometry.SheafCohomology.Projective.ModuleProductElements.moduleProductElement_ext (fun b : AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 0 => AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U 0 b.val)
  intro a
  exact (ConcreteCategory.congr_hom (Augmentation.map_π π U M a) x).trans
    (AlgebraicGeometry.SheafCohomology.Projective.BaseZeroCycleCoordinates.orderedBaseTopSectionsZeroCyclesAddEquiv_coordinate π M U hU x a).symm

theorem map_d (M : X.Modules) (hU : iSup U = ⊤) :
    Augmentation.map π U M ≫ (AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U).d 0 1 = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U).d 0 1 (Augmentation.map π U M x) = 0
  rw [map_eq_zeroCycle π U M hU]
  exact (AlgebraicGeometry.SheafCohomology.Projective.ZeroCyclesLinearSections.orderedBaseTopSectionsZeroCyclesLinearEquiv π M U hU x).property

theorem map_mono (M : X.Modules) (hU : iSup U = ⊤) : Mono (Augmentation.map π U M) := by
  rw [ModuleCat.mono_iff_injective]
  intro x y hxy
  apply (AlgebraicGeometry.SheafCohomology.Projective.ZeroCyclesLinearSections.orderedBaseTopSectionsZeroCyclesLinearEquiv π M U hU).injective
  apply Subtype.ext
  exact (map_eq_zeroCycle π U M hU x).symm.trans (hxy.trans (map_eq_zeroCycle π U M hU y))

theorem exact (M : X.Modules) (hU : iSup U = ⊤) :
    (ShortComplex.mk (Augmentation.map π U M) ((AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U).d 0 1) (map_d π U M hU)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro y hy
  let e := AlgebraicGeometry.SheafCohomology.Projective.ZeroCyclesLinearSections.orderedBaseTopSectionsZeroCyclesLinearEquiv π M U hU
  refine ⟨e.symm ⟨y, hy⟩, ?_⟩
  exact (map_eq_zeroCycle π U M hU _).trans (congrArg Subtype.val (e.apply_symm_apply ⟨y, hy⟩))

@[reassoc]
theorem cechMap_π {M N : X.Modules} (f : M ⟶ N) (a : AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 0) :
    ((AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechFunctor.Scheme.Modules.orderedBaseCechComplexFunctor π U).map f).f 0 ≫
        Pi.π (fun b : AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 0 => AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π N U 0 b.val) a =
      Pi.π (fun b : AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 0 => AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U 0 b.val) a ≫
        ((AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheafFunctor π).map f).app (op (∏ᶜ fun k : Fin 1 => U (a.val k))) :=
  Pi.map_π (fun b : AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 0 =>
    ((AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheafFunctor π).map f).app (op (∏ᶜ fun k : Fin 1 => U (b.val k)))) a

theorem naturality {M N : X.Modules} (f : M ⟶ N) :
    (sections π).map f ≫ Augmentation.map π U N =
      Augmentation.map π U M ≫ ((AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechFunctor.Scheme.Modules.orderedBaseCechComplexFunctor π U).map f).f 0 := by
  apply Pi.hom_ext (f := fun b : AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 0 => AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π N U 0 b.val)
  intro a
  rw [Category.assoc, Augmentation.map_π, Category.assoc, cechMap_π, map_π_assoc]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (PresheafOfModules.naturality_apply f.val
    (homOfLE (show (∏ᶜ fun k : Fin 1 => U (a.val k)) ≤ ⊤ from le_top)).op x).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.Augmentation
