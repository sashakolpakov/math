import OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseZeroCyclesSections

/-! # Base Zero Cycle Coordinates -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseZeroCycleCoordinates

noncomputable section

/-! The direct section-to-zero-cycle comparisons restrict each section to its actual intersection. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
open _root_.AlgebraicGeometry.Scheme.Modules
universe u
variable {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
variable {ι : Type u} (U : ι → X.Opens)

theorem baseTopSectionsZeroCyclesAddEquiv_coordinate (hU : iSup U = ⊤)
    (x : Γ(M, ⊤)) (a : Fin 1 → ι) :
    (Pi.π (fun b : Fin 1 → ι => Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U 0 b) a)
        (BaseZeroCyclesSections.baseTopSectionsZeroCyclesAddEquiv π M U hU x).val =
      M.presheaf.map (homOfLE (show (∏ᶜ fun k : Fin 1 => U (a k)) ≤ ⊤ from le_top)).op x := by
  let z := BaseZeroCyclesSections.baseTopSectionsZeroCyclesAddEquiv π M U hU x
  let t := Cech.TopZeroCycles.TopCat.Sheaf.cechTopSectionsZeroCyclesEquiv U (Module.ProjectiveAffine.ModuleSheaf.sheaf M) hU x
  have heq : BaseZeroCyclesSections.baseCechZeroCyclesForgetEquiv π M U z = t :=
    (BaseZeroCyclesSections.baseCechZeroCyclesForgetEquiv π M U).apply_symm_apply t
  have hv : (BaseCechForget.Scheme.Modules.baseCechComplexForgetIso π M U).hom.f 0 z.val = t.val :=
    congrArg Subtype.val heq
  have hp := ConcreteCategory.congr_hom (BaseCechForget.Scheme.Modules.baseCechComplexForgetIso_component π M U 0 a) z.val
  change (Pi.π (fun b : Fin 1 → ι => M.presheaf.obj
      (op (∏ᶜ fun k : Fin 1 => U (b k)))) a)
        ((BaseCechForget.Scheme.Modules.baseCechComplexForgetIso π M U).hom.f 0 z.val) =
      (Pi.π (fun b : Fin 1 → ι => Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U 0 b) a) z.val at hp
  have ht := Cech.TopZeroCycles.TopCat.Sheaf.cechTopSectionsZeroCyclesEquiv_coordinate U
    (Module.ProjectiveAffine.ModuleSheaf.sheaf M) hU x a
  rw [Cech.Cochains.TopologicalSpace.cechCochainAddEquiv_apply] at ht
  rw [hv] at hp
  exact hp.symm.trans ht

theorem orderedBaseTopSectionsZeroCyclesAddEquiv_coordinate [LinearOrder ι]
    (hU : iSup U = ⊤) (x : Γ(M, ⊤)) (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 0) :
    (Pi.π (fun b : OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 0 => Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U 0 b.val) a)
        (BaseZeroCyclesSections.orderedBaseTopSectionsZeroCyclesAddEquiv π M U hU x).val =
      M.presheaf.map (homOfLE (show (∏ᶜ fun k : Fin 1 => U (a.val k)) ≤ ⊤ from le_top)).op x := by
  have hp := ConcreteCategory.congr_hom (OrderedBaseCechComparison.Scheme.Modules.baseCechToOrderedF_comp_π π M U 0 a)
    (BaseZeroCyclesSections.baseTopSectionsZeroCyclesAddEquiv π M U hU x).val
  exact hp.trans (baseTopSectionsZeroCyclesAddEquiv_coordinate π M U hU x a.val)

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseZeroCycleCoordinates
