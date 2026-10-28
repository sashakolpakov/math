import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.PointFaithfulness

/-! # Dual Map Faithfulness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! With the original-family isomorphism fixed, Poincare compatibility uniquely determines its dual map, over arbitrary bases. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

theorem Dual.Data.DualAbelianData.dualMap_eq_of_poincare_and_familyIso
    {S : Scheme.{u}} {g : ℕ} {B : Abelian.Schemes.AbelianScheme g S}
    (E : Dual.Data.DualAbelianData B) {A C : Over S} (e : A ≅ B.scheme) (d q : C ⟶ E.abelian.scheme)
    (h : Line.Bundles.LineBundle.pullbackClass (d ⊗ₘ e.hom).left (Line.Bundles.LineBundle.classOf E.poincare) =
      Line.Bundles.LineBundle.pullbackClass (q ⊗ₘ e.hom).left (Line.Bundles.LineBundle.classOf E.poincare)) : d = q := by
  let l := 𝟙 C ⊗ₘ e.inv
  have hd : l ≫ (d ⊗ₘ e.hom) = d ⊗ₘ 𝟙 B.scheme := by
    dsimp only [l]
    rw [tensorHom_comp_tensorHom, Category.id_comp, e.inv_hom_id]
  have hq : l ≫ (q ⊗ₘ e.hom) = q ⊗ₘ 𝟙 B.scheme := by
    dsimp only [l]
    rw [tensorHom_comp_tensorHom, Category.id_comp, e.inv_hom_id]
  have H := congrArg (Line.Bundles.LineBundle.pullbackClass l.left) h
  rw [← Line.Bundles.LineBundle.pullbackClass_comp, ← Line.Bundles.LineBundle.pullbackClass_comp,
    ← Over.comp_left, ← Over.comp_left, hd, hq] at H
  exact E.hom_eq_of_poincarePullbackClass d q H

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
