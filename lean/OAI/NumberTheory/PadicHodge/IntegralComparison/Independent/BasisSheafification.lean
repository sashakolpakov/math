import Mathlib

/-! # Basis Sheafification -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Independent.BasisSheafification

noncomputable section

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

universe u v w z

variable {C : Type u} [Category.{v} C] {X : TopCat.{w}} {ι : Type z}
  (B : ι → Opens X) (hB : Opens.IsBasis (Set.range B))
  (P : X.Presheaf C) (F : TopCat.Sheaf C X)
  (e : (inducedFunctor B).op ⋙ P ≅ (inducedFunctor B).op ⋙ F.obj)

def toSheaf : P ⟶ F.obj := TopCat.Sheaf.restrictHomEquivHom P F hB e.hom

theorem toSheaf_app (i : ι) :
    (toSheaf B hB P F e).app (op (B i)) = e.hom.app (op i) :=
  TopCat.Sheaf.extend_hom_app P F hB e.hom i

variable [HasWeakSheafify (Opens.grothendieckTopology X) C]

def forward : (presheafToSheaf (Opens.grothendieckTopology X) C).obj P ⟶ F :=
  ⟨sheafifyLift (Opens.grothendieckTopology X) (toSheaf B hB P F e) F.property⟩

theorem unit_forward :
    toSheafify (Opens.grothendieckTopology X) P ≫ (forward B hB P F e).hom =
      toSheaf B hB P F e :=
  toSheafify_sheafifyLift _ _ _

def backward : F ⟶ (presheafToSheaf (Opens.grothendieckTopology X) C).obj P :=
  ⟨TopCat.Sheaf.restrictHomEquivHom F.obj
    ((presheafToSheaf (Opens.grothendieckTopology X) C).obj P) hB
    (e.inv ≫ Functor.whiskerLeft (inducedFunctor B).op (toSheafify (Opens.grothendieckTopology X) P))⟩

theorem backward_app (i : ι) :
    (backward B hB P F e).hom.app (op (B i)) =
      e.inv.app (op i) ≫ (toSheafify (Opens.grothendieckTopology X) P).app (op (B i)) :=
  TopCat.Sheaf.extend_hom_app F.obj
    ((presheafToSheaf (Opens.grothendieckTopology X) C).obj P) hB _ i

theorem unit_forward_app (i : ι) :
    (toSheafify (Opens.grothendieckTopology X) P).app (op (B i)) ≫
      (forward B hB P F e).hom.app (op (B i)) = e.hom.app (op i) := by
  exact (congrArg (fun a => a.app (op (B i))) (unit_forward B hB P F e)).trans
    (toSheaf_app B hB P F e i)

def iso : (presheafToSheaf (Opens.grothendieckTopology X) C).obj P ≅ F where
  hom := forward B hB P F e
  inv := backward B hB P F e
  hom_inv_id := by
    apply Sheaf.hom_ext
    apply sheafify_hom_ext (Opens.grothendieckTopology X) _ _
      ((presheafToSheaf (Opens.grothendieckTopology X) C).obj P).property
    change toSheafify (Opens.grothendieckTopology X) P ≫
      ((forward B hB P F e).hom ≫ (backward B hB P F e).hom) =
      toSheafify (Opens.grothendieckTopology X) P ≫ 𝟙 _
    rw [← Category.assoc, unit_forward, Category.comp_id]
    apply TopCat.Sheaf.hom_ext P
      ((presheafToSheaf (Opens.grothendieckTopology X) C).obj P) hB
    intro i
    change (toSheaf B hB P F e).app (op (B i)) ≫
      (backward B hB P F e).hom.app (op (B i)) = _
    rw [toSheaf_app, backward_app]
    simp
  inv_hom_id := by
    apply Sheaf.hom_ext
    apply TopCat.Sheaf.hom_ext F.obj F hB
    intro i
    change (backward B hB P F e).hom.app (op (B i)) ≫
      (forward B hB P F e).hom.app (op (B i)) = 𝟙 _
    rw [backward_app, Category.assoc, unit_forward_app]
    simp

theorem component (i : ι) :
    (toSheafify (Opens.grothendieckTopology X) P).app (op (B i)) ≫
      (iso B hB P F e).hom.hom.app (op (B i)) = e.hom.app (op i) :=
  unit_forward_app B hB P F e i

include hB e in
theorem unit_isIso (i : ι) :
    IsIso ((toSheafify (Opens.grothendieckTopology X) P).app (op (B i))) := by
  let a := (iso B hB P F e).hom.hom.app (op (B i))
  have : IsIso a := (((sheafToPresheaf (Opens.grothendieckTopology X) C).mapIso
    (iso B hB P F e)).app (op (B i))).isIso_hom
  have : IsIso ((toSheafify (Opens.grothendieckTopology X) P).app (op (B i)) ≫ a) := by
    rw [show _ ≫ a = e.hom.app (op i) from component B hB P F e i]
    infer_instance
  exact IsIso.of_isIso_comp_right _ a

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Independent.BasisSheafification
