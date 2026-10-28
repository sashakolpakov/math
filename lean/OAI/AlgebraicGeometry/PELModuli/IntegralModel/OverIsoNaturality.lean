import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Cartesian.FamilyMorphismComparison

/-! # Over Iso Naturality -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.OverIsoNaturality

noncomputable section

/-! Exact specialization equations imply naturality of the actual
generic-fiber isomorphisms of two scheme models. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem over_model_iso_naturality {S T : Scheme.{0}} (b : T ⟶ S)
    {M N : Over S} {X Y : Over T}
    (eX : (Over.pullback b).obj M ≅ X) (eY : (Over.pullback b).obj N ≅ Y)
    (f : X ⟶ Y) (m : M ⟶ N)
    (hs : (eX.inv.left ≫ pullback.fst M.hom b) ≫ m.left =
      f.left ≫ (eY.inv.left ≫ pullback.fst N.hom b)) :
    (Over.pullback b).map m ≫ eY.hom = eX.hom ≫ f := by
  let F := Over.pullback b
  have hi : eX.inv ≫ F.map m = f ≫ eY.inv := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · change (eX.inv.left ≫ (F.map m).left) ≫ pullback.fst N.hom b =
        (f.left ≫ eY.inv.left) ≫ pullback.fst N.hom b
      rw [Category.assoc, Cartesian.FamilyMorphismComparison.over_pullback_map_fst, ← Category.assoc, hs, Category.assoc]
    · exact (eX.inv ≫ F.map m).w.trans (f ≫ eY.inv).w.symm
  calc
    F.map m ≫ eY.hom = (eX.hom ≫ (eX.inv ≫ F.map m)) ≫ eY.hom := by
      rw [Iso.hom_inv_id_assoc]
    _ = (eX.hom ≫ (f ≫ eY.inv)) ≫ eY.hom :=
      congrArg (fun k => (eX.hom ≫ k) ≫ eY.hom) hi
    _ = eX.hom ≫ f := by simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.OverIsoNaturality
