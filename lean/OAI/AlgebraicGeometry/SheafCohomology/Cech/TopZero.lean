import OAI.AlgebraicGeometry.SheafCohomology.Cech.DegreeZero

/-! # Top Zero -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Cech.TopZero.TopCat.Sheaf

noncomputable section

open _root_.TopCat
open _root_.TopCat.Sheaf

/-! The degree-zero Čech injection in terms of literal sections over the whole space. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
universe u
variable {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X)

def cechTopSectionsToHZero (F : Sheaf AddCommGrpCat.{u} X) :
    F.obj.obj (op ⊤) ⟶ ((cechComplexFunctor U).obj F.obj).homology 0 :=
  (CategoryTheory.Sheaf.ΓNatIsoSheafSections
    (Opens.grothendieckTopology X) AddCommGrpCat.{u} isTerminalTop).inv.app F ≫
      DegreeZero.TopCat.Sheaf.cechGlobalSectionsToHZero U F

theorem cechTopSectionsToHZero_mono (F : Sheaf AddCommGrpCat.{u} X)
    (hU : ⨆ i, U i = ⊤) : Mono (cechTopSectionsToHZero U F) := by
  let : Mono (DegreeZero.TopCat.Sheaf.cechGlobalSectionsToHZero U F) := DegreeZero.TopCat.Sheaf.cechGlobalSectionsToHZero_mono U F hU
  unfold cechTopSectionsToHZero
  let : IsIso ((CategoryTheory.Sheaf.ΓNatIsoSheafSections
    (Opens.grothendieckTopology X) AddCommGrpCat.{u} isTerminalTop).inv.app F) :=
    inferInstanceAs (IsIso ((CategoryTheory.Sheaf.ΓNatIsoSheafSections
      (Opens.grothendieckTopology X) AddCommGrpCat.{u} isTerminalTop).app F).inv)
  infer_instance

theorem cechTopSectionsToHZero_naturality
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) :
    cechTopSectionsToHZero U F ≫
      HomologicalComplex.homologyMap ((cechComplexFunctor U).map f.hom) 0 =
    f.hom.app (op ⊤) ≫ cechTopSectionsToHZero U G := by
  unfold cechTopSectionsToHZero
  rw [Category.assoc, DegreeZero.TopCat.Sheaf.cechGlobalSectionsToHZero_naturality, ← Category.assoc]
  erw [← (CategoryTheory.Sheaf.ΓNatIsoSheafSections
    (Opens.grothendieckTopology X) AddCommGrpCat.{u} isTerminalTop).inv.naturality f]
  rfl

end

end OAI.AlgebraicGeometry.SheafCohomology.Cech.TopZero.TopCat.Sheaf
