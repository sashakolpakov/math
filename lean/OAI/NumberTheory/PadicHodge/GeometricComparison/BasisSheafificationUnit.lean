import OAI.NumberTheory.PadicHodge.GeometricComparison.BasisSheafificationTo

/-! # Basis Sheafification Unit -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.BasisSheafificationUnit.BasisSheafification

noncomputable section

/-! The canonical sheafification unit is an isomorphism on each basis open where the original presheaf agrees with a sheaf. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

universe u v w z

variable {C : Type u} [Category.{v} C] {X : TopCat.{w}} {ι : Type z}
  (B : ι → Opens X) (hB : Opens.IsBasis (Set.range B))
  (P : X.Presheaf C) (F : TopCat.Sheaf C X)
  (e : (inducedFunctor B).op ⋙ P ≅ (inducedFunctor B).op ⋙ F.obj)
  [HasWeakSheafify (Opens.grothendieckTopology X) C]

theorem unit_iso : toSheafify (Opens.grothendieckTopology X) P ≫
    (BasisSheafificationTo.BasisSheafification.iso B hB P F e).hom.hom = BasisSheafificationTo.BasisSheafification.toSheaf B hB P F e :=
  toSheafify_sheafifyLift (Opens.grothendieckTopology X) (BasisSheafificationTo.BasisSheafification.toSheaf B hB P F e) F.property

theorem unit_iso_app (i : ι) :
    (toSheafify (Opens.grothendieckTopology X) P).app (op (B i)) ≫
      (BasisSheafificationTo.BasisSheafification.iso B hB P F e).hom.hom.app (op (B i)) = e.hom.app (op i) :=
  (congrArg (fun a => a.app (op (B i))) (unit_iso B hB P F e)).trans
    (BasisSheafificationTo.BasisSheafification.toSheaf_app B hB P F e i)

include hB e in
theorem unit_app_isIso (i : ι) :
    IsIso ((toSheafify (Opens.grothendieckTopology X) P).app (op (B i))) := by
  have hi : IsIso ((BasisSheafificationTo.BasisSheafification.iso B hB P F e).hom.hom.app (op (B i))) :=
    (((sheafToPresheaf (Opens.grothendieckTopology X) C).mapIso (BasisSheafificationTo.BasisSheafification.iso B hB P F e)).app
      (op (B i))).isIso_hom
  have hc : IsIso ((toSheafify (Opens.grothendieckTopology X) P).app (op (B i)) ≫
      (BasisSheafificationTo.BasisSheafification.iso B hB P F e).hom.hom.app (op (B i))) :=
    (unit_iso_app B hB P F e i).symm ▸ inferInstance
  exact (isIso_comp_right_iff
    ((toSheafify (Opens.grothendieckTopology X) P).app (op (B i)))
    ((BasisSheafificationTo.BasisSheafification.iso B hB P F e).hom.hom.app (op (B i)))).mp hc

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.BasisSheafificationUnit.BasisSheafification
