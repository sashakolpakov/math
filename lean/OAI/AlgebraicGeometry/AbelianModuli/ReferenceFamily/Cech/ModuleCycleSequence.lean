import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.ModuleAugmentation
import OAI.AlgebraicGeometry.SheafCohomology.Cech.Resolution
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! # Module Cycle Sequence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.ModuleCycleSequence

noncomputable section

section

/-! The exactness of the original Cech sheaf resolution is reflected
into its actual algebraic module enhancement. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open _root_.TopCat.Sheaf

theorem shortComplexExact_of_equal_maps {C : Type*} [Category* C] [Abelian C]
    {A B D : C} {f f' : A ⟶ B} {g g' : B ⟶ D}
    {w : f ≫ g = 0} {w' : f' ≫ g' = 0} (hf : f = f') (hg : g = g')
    (h : (ShortComplex.mk f' g' w').Exact) : (ShortComplex.mk f g w).Exact := by
  subst f'
  subst g'
  exact h

variable (X : Scheme.{0})

def moduleAbelianForget : X.Modules ⥤ TopCat.Sheaf AddCommGrpCat.{0} X :=
  SheafOfModules.toSheaf X.ringCatSheaf

instance moduleAbelianForget_additive : (moduleAbelianForget X).Additive where
  map_add := rfl

instance moduleAbelianForget_preservesZeroMorphisms : (moduleAbelianForget X).PreservesZeroMorphisms where
  map_zero _ _ := rfl

instance moduleAbelianForget_faithful : (moduleAbelianForget X).Faithful where
  map_injective h := by
    apply Scheme.Modules.hom_ext
    intro U
    exact congrArg (fun f => f.hom.app (.op U)) h

instance moduleAbelianForget_preservesFiniteLimits : PreservesFiniteLimits (moduleAbelianForget X) :=
  inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf.{0} X.ringCatSheaf))

instance moduleAbelianForget_preservesFiniteColimits : PreservesFiniteColimits (moduleAbelianForget X) :=
  ModuleHomOf.moduleSheaf_toSheaf_preservesFiniteColimits X

theorem moduleExact_of_underlying (S : ShortComplex X.Modules)
    (h : (S.map (moduleAbelianForget X)).Exact) : S.Exact :=
  (S.exact_map_iff_of_faithful (moduleAbelianForget X)).mp h

variable {I : Type} (U : I → X.Opens) (hU : iSup U = ⊤)
include hU

theorem cechModuleAugmentedShortComplex_exact : (ModuleAugmentation.cechModuleAugmentedShortComplex X U).Exact := by
  apply moduleExact_of_underlying X
  change (ShortComplex.mk ((moduleAbelianForget X).map (ModuleAugmentation.cechModuleAugmentation X U))
    ((moduleAbelianForget X).map (ModuleDifferential.cechModuleDifferential X U 0)) _).Exact
  exact shortComplexExact_of_equal_maps (ModuleAugmentation.cechModuleAugmentation_underlying X U)
    (ModuleDifferential.cechModuleDifferential_underlying X U 0)
    (SheafCohomology.Cech.ZeroExact.TopCat.Sheaf.cechAugmentedShortComplex_exact (TermModules.structureAbelianSheaf X) U hU)

theorem cechModuleShortComplex_exact (n : ℕ) : (ModuleAugmentation.cechModuleShortComplex X U n).Exact := by
  apply moduleExact_of_underlying X
  change (ShortComplex.mk ((moduleAbelianForget X).map (ModuleDifferential.cechModuleDifferential X U n))
    ((moduleAbelianForget X).map (ModuleDifferential.cechModuleDifferential X U (n + 1))) _).Exact
  exact shortComplexExact_of_equal_maps (ModuleDifferential.cechModuleDifferential_underlying X U n)
    (ModuleDifferential.cechModuleDifferential_underlying X U (n + 1))
    (SheafCohomology.Cech.PositiveExact.TopCat.Sheaf.cechShortComplex_exact (TermModules.structureAbelianSheaf X) U hU n)

theorem cechModuleAugmentation_mono : Mono (ModuleAugmentation.cechModuleAugmentation X U) := by
  have h : Mono ((moduleAbelianForget X).map (ModuleAugmentation.cechModuleAugmentation X U)) :=
    (ModuleAugmentation.cechModuleAugmentation_underlying X U).symm ▸ SheafCohomology.Cech.Resolution.TopCat.Sheaf.cechAugmentation_mono (TermModules.structureAbelianSheaf X) U hU
  exact (moduleAbelianForget X).mono_of_mono_map h

end

/-! The original degree-one Cech cycles fit into an actual short exact
sequence of algebraic modules. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Scheme.{0}) {I : Type} (U : I → X.Opens)

def cechModuleOneCycles : X.Modules := kernel (ModuleDifferential.cechModuleDifferential X U 1)

def cechModuleToOneCycles : TermModules.cechTermModule X U 0 ⟶ cechModuleOneCycles X U :=
  kernel.lift (ModuleDifferential.cechModuleDifferential X U 1) (ModuleDifferential.cechModuleDifferential X U 0)
    (ModuleAugmentation.cechModuleDifferential_comp X U 0)

theorem cechModuleAugmentation_toOneCycles :
    ModuleAugmentation.cechModuleAugmentation X U ≫ cechModuleToOneCycles X U = 0 := by
  apply (cancel_mono (kernel.ι (ModuleDifferential.cechModuleDifferential X U 1))).mp
  have hq : cechModuleToOneCycles X U ≫ kernel.ι (ModuleDifferential.cechModuleDifferential X U 1) =
      ModuleDifferential.cechModuleDifferential X U 0 := kernel.lift_ι _ _ _
  exact (Category.assoc _ _ _).trans
    ((congrArg (ModuleAugmentation.cechModuleAugmentation X U ≫ ·) hq).trans
      ((ModuleAugmentation.cechModuleAugmentation_comp X U).trans (zero_comp).symm))

def cechModuleCycleSequence : ShortComplex X.Modules :=
  ShortComplex.mk (ModuleAugmentation.cechModuleAugmentation X U) (cechModuleToOneCycles X U)
    (cechModuleAugmentation_toOneCycles X U)

def cechModuleCycleSequenceMap : cechModuleCycleSequence X U ⟶ ModuleAugmentation.cechModuleAugmentedShortComplex X U where
  τ₁ := 𝟙 _
  τ₂ := 𝟙 _
  τ₃ := kernel.ι (ModuleDifferential.cechModuleDifferential X U 1)
  comm₁₂ := (Category.id_comp _).trans (Category.comp_id _).symm
  comm₂₃ := (Category.id_comp _).trans (kernel.lift_ι _ _ _).symm

theorem cechModuleCycleSequence_shortExact (hU : iSup U = ⊤) :
    (cechModuleCycleSequence X U).ShortExact := by
  have hm : Mono (ModuleAugmentation.cechModuleAugmentation X U) := cechModuleAugmentation_mono X U hU
  have he : Epi (cechModuleToOneCycles X U) :=
    (cechModuleShortComplex_exact X U hU 0).epi_kernelLift
  refine { mono_f := hm, epi_g := he, exact := ?_ }
  let φ := cechModuleCycleSequenceMap X U
  let : Epi φ.τ₁ := inferInstanceAs (Epi (𝟙 (HilbertConstruction.Line.Bundles.structureModule X)))
  let : IsIso φ.τ₂ := inferInstanceAs (IsIso (𝟙 (TermModules.cechTermModule X U 0)))
  let : Mono φ.τ₃ := inferInstanceAs (Mono (kernel.ι (ModuleDifferential.cechModuleDifferential X U 1)))
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr
    (cechModuleAugmentedShortComplex_exact X U hU)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.ModuleCycleSequence
