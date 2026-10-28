import Mathlib.Topology.Sheaves.SheafCondition.Sites
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Whiskering

/-! # Basis Sheafification To -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.BasisSheafificationTo.BasisSheafification

noncomputable section

/-! Agreement with a sheaf on an open basis identifies the actual sheafification. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

universe u v w z

variable {C : Type u} [Category.{v} C] {X : TopCat.{w}} {ι : Type z}
  (B : ι → Opens X) (hB : Opens.IsBasis (Set.range B))
  (P : X.Presheaf C) (F : TopCat.Sheaf C X)
  (e : (inducedFunctor B).op ⋙ P ≅ (inducedFunctor B).op ⋙ F.obj)

def toSheaf : P ⟶ F.obj := TopCat.Sheaf.restrictHomEquivHom P F hB e.hom

theorem toSheaf_app (i : ι) : (toSheaf B hB P F e).app (op (B i)) = e.hom.app (op i) :=
  TopCat.Sheaf.extend_hom_app P F hB e.hom i

theorem toSheaf_cancel (G : TopCat.Sheaf C X) {f g : F.obj ⟶ G.obj}
    (h : toSheaf B hB P F e ≫ f = toSheaf B hB P F e ≫ g) : f = g := by
  apply TopCat.Sheaf.hom_ext F.obj G hB
  intro i
  apply (cancel_epi (e.hom.app (op i))).mp
  have hi := congrArg (fun a => a.app (op (B i))) h
  change (toSheaf B hB P F e).app (op (B i)) ≫ f.app (op (B i)) =
    (toSheaf B hB P F e).app (op (B i)) ≫ g.app (op (B i)) at hi
  exact (toSheaf_app B hB P F e i) ▸ hi

variable [HasWeakSheafify (Opens.grothendieckTopology X) C]

def fromSheaf : F.obj ⟶ sheafify (Opens.grothendieckTopology X) P :=
  TopCat.Sheaf.restrictHomEquivHom F.obj
    ((presheafToSheaf (Opens.grothendieckTopology X) C).obj P) hB
      (e.inv ≫ Functor.whiskerLeft (inducedFunctor B).op (toSheafify (Opens.grothendieckTopology X) P))

theorem toSheaf_fromSheaf : toSheaf B hB P F e ≫ fromSheaf B hB P F e =
    toSheafify (Opens.grothendieckTopology X) P := by
  apply TopCat.Sheaf.hom_ext P ((presheafToSheaf (Opens.grothendieckTopology X) C).obj P) hB
  intro i
  change (toSheaf B hB P F e).app (op (B i)) ≫
    (fromSheaf B hB P F e).app (op (B i)) = _
  rw [toSheaf_app]
  exact (congrArg (fun m => e.hom.app (op i) ≫ m)
    (TopCat.Sheaf.extend_hom_app F.obj
      ((presheafToSheaf (Opens.grothendieckTopology X) C).obj P) hB
      (e.inv ≫ Functor.whiskerLeft (inducedFunctor B).op
        (toSheafify (Opens.grothendieckTopology X) P)) i)).trans
    (Iso.hom_inv_id_app_assoc e (op i) _)

def iso : (presheafToSheaf (Opens.grothendieckTopology X) C).obj P ≅ F where
  hom := ⟨sheafifyLift (Opens.grothendieckTopology X) (toSheaf B hB P F e) F.property⟩
  inv := ⟨fromSheaf B hB P F e⟩
  hom_inv_id := by
    apply Sheaf.hom_ext
    apply sheafify_hom_ext _ _ _
      ((presheafToSheaf (Opens.grothendieckTopology X) C).obj P).property
    change toSheafify (Opens.grothendieckTopology X) P ≫
      (sheafifyLift (Opens.grothendieckTopology X) (toSheaf B hB P F e) F.property ≫
        fromSheaf B hB P F e) = toSheafify (Opens.grothendieckTopology X) P ≫ 𝟙 _
    rw [← Category.assoc, toSheafify_sheafifyLift, Category.comp_id, toSheaf_fromSheaf]
  inv_hom_id := by
    apply Sheaf.hom_ext
    apply toSheaf_cancel B hB P F e F
    change toSheaf B hB P F e ≫
      (fromSheaf B hB P F e ≫
        sheafifyLift (Opens.grothendieckTopology X) (toSheaf B hB P F e) F.property) =
      toSheaf B hB P F e ≫ 𝟙 _
    rw [← Category.assoc, toSheaf_fromSheaf, toSheafify_sheafifyLift, Category.comp_id]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.BasisSheafificationTo.BasisSheafification
