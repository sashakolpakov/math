import OAI.AlgebraicGeometry.SheafCohomology.Cech.ZeroSurjective

/-! # Top Zero Cycles -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Cech.TopZeroCycles

noncomputable section

open _root_.TopCat
open _root_.TopCat.Sheaf

/-! The direct restriction map identifies actual top sections with native Čech zero cycles. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
universe u
namespace TopCat.Sheaf
variable {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X)
    (F : Sheaf AddCommGrpCat.{u} X)

abbrev nativeCechZeroCycles := (((cechComplexFunctor U).obj F.obj).d 0 1).hom.ker

def cechTopSectionsAugmentation :
    F.obj.obj (op ⊤) ⟶ ((cechComplexFunctor U).obj F.obj).X 0 :=
  (CategoryTheory.Sheaf.ΓNatIsoSheafSections
    (Opens.grothendieckTopology X) AddCommGrpCat.{u} isTerminalTop).inv.app F ≫
      GlobalSections.TopCat.Sheaf.cechGlobalSectionsAugmentation F U

theorem cechTopSectionsAugmentation_comp_d :
    cechTopSectionsAugmentation U F ≫ ((cechComplexFunctor U).obj F.obj).d 0 1 = 0 := by
  rw [cechTopSectionsAugmentation, Category.assoc, GlobalSections.TopCat.Sheaf.cechGlobalSectionsAugmentation_comp_d, comp_zero]

def cechTopSectionsToZeroCycles : F.obj.obj (op ⊤) →+ nativeCechZeroCycles U F where
  toFun x := ⟨cechTopSectionsAugmentation U F x,
    ConcreteCategory.congr_hom (cechTopSectionsAugmentation_comp_d U F) x⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ x y)

theorem cechTopSectionsToZeroCycles_bijective (hU : iSup U = ⊤) :
    Function.Bijective (cechTopSectionsToZeroCycles U F) := by
  let e := (CategoryTheory.Sheaf.ΓNatIsoSheafSections
    (Opens.grothendieckTopology X) AddCommGrpCat.{u} isTerminalTop).app F
  have hinj : Function.Injective (GlobalSections.TopCat.Sheaf.cechGlobalSectionsAugmentation F U) :=
    (AddCommGrpCat.mono_iff_injective _).mp (InjectiveComparison.TopCat.Sheaf.cechGlobalSectionsAugmentation_mono U F hU)
  constructor
  · intro x y h
    apply e.symm.addCommGroupIsoToAddEquiv.injective
    apply hinj
    exact congrArg Subtype.val h
  · intro z
    obtain ⟨x, hx⟩ := (ShortComplex.ab_exact_iff _).mp
      (InjectiveComparison.TopCat.Sheaf.cechGlobalSectionsNativeShortComplex_exact U F hU) z.val z.property
    refine ⟨e.hom x, Subtype.ext ?_⟩
    change GlobalSections.TopCat.Sheaf.cechGlobalSectionsAugmentation F U (e.inv (e.hom x)) = z.val
    rw [Iso.hom_inv_id_apply]
    exact hx

def cechTopSectionsZeroCyclesEquiv (hU : iSup U = ⊤) :
    F.obj.obj (op ⊤) ≃+ nativeCechZeroCycles U F :=
  AddEquiv.ofBijective (cechTopSectionsToZeroCycles U F)
    (cechTopSectionsToZeroCycles_bijective U F hU)

theorem cechTopSectionsZeroCyclesEquiv_coordinate (hU : iSup U = ⊤)
    (x : F.obj.obj (op ⊤)) (i : Fin 1 → ι) :
    Cochains.TopologicalSpace.cechCochainAddEquiv F.obj U 0 (cechTopSectionsZeroCyclesEquiv U F hU x).val i =
      F.obj.map (homOfLE (show (∏ᶜ fun k : Fin 1 => U (i k)) ≤ ⊤ from le_top)).op x := by
  let e := (CategoryTheory.Sheaf.ΓNatIsoSheafSections
    (Opens.grothendieckTopology X) AddCommGrpCat.{u} isTerminalTop).app F
  change Cochains.TopologicalSpace.cechCochainAddEquiv F.obj U 0 (GlobalSections.TopCat.Sheaf.cechGlobalSectionsAugmentation F U (e.inv x)) i = _
  rw [GlobalSections.TopCat.Sheaf.cechGlobalSectionsAugmentation_coordinate]
  exact congrArg (fun y => F.obj.map
    (homOfLE (show (∏ᶜ fun k : Fin 1 => U (i k)) ≤ ⊤ from le_top)).op y)
      (Iso.inv_hom_id_apply e x)

end TopCat.Sheaf

end

end OAI.AlgebraicGeometry.SheafCohomology.Cech.TopZeroCycles
