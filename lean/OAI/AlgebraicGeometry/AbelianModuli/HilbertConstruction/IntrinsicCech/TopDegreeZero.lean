import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.DegreeZero

/-! # Top Degree Zero -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.TopDegreeZero

noncomputable section

/-! The degree-zero Čech injection in terms of literal sections over the whole space. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
universe u
variable {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X)

def cechTopSectionsToHZero (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    F.obj.obj (op ⊤) ⟶ ((cechComplexFunctor U).obj F.obj).homology 0 :=
  (CategoryTheory.Sheaf.ΓNatIsoSheafSections
    (Opens.grothendieckTopology X) AddCommGrpCat.{u} isTerminalTop).inv.app F ≫
      DegreeZero.cechGlobalSectionsToHZero U F

theorem cechTopSectionsToHZero_mono (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hU : ⨆ i, U i = ⊤) : Mono (cechTopSectionsToHZero U F) := by
  let : Mono (DegreeZero.cechGlobalSectionsToHZero U F) := DegreeZero.cechGlobalSectionsToHZero_mono U F hU
  unfold cechTopSectionsToHZero
  let : IsIso ((CategoryTheory.Sheaf.ΓNatIsoSheafSections
    (Opens.grothendieckTopology X) AddCommGrpCat.{u} isTerminalTop).inv.app F) :=
    inferInstanceAs (IsIso ((CategoryTheory.Sheaf.ΓNatIsoSheafSections
      (Opens.grothendieckTopology X) AddCommGrpCat.{u} isTerminalTop).app F).inv)
  infer_instance

theorem cechTopSectionsToHZero_naturality
    {F G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (f : F ⟶ G) :
    cechTopSectionsToHZero U F ≫
      HomologicalComplex.homologyMap ((cechComplexFunctor U).map f.hom) 0 =
    f.hom.app (op ⊤) ≫ cechTopSectionsToHZero U G := by
  unfold cechTopSectionsToHZero
  rw [Category.assoc, DegreeZero.cechGlobalSectionsToHZero_naturality, ← Category.assoc]
  erw [← (CategoryTheory.Sheaf.ΓNatIsoSheafSections
    (Opens.grothendieckTopology X) AddCommGrpCat.{u} isTerminalTop).inv.naturality f]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.TopDegreeZero
