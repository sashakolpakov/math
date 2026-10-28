import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Embedding -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.Embedding.PullbackEmbedding

noncomputable section

/-! A fiber product over a separated base embeds as a closed subscheme
of the ordinary product. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits

universe u

theorem closed {S X Y : Scheme.{u}} [S.IsSeparated] (f : X ⟶ S) (g : Y ⟶ S) :
    IsClosedImmersion (prod.lift (pullback.fst f g) (pullback.snd f g)) := by
  let e := pullback.congrHom (terminal.comp_from f) (terminal.comp_from g)
  have he : prod.lift (pullback.fst f g) (pullback.snd f g) =
      pullback.mapDesc f g (terminal.from S) ≫ e.hom ≫ (prodIsoPullback X Y).inv := by
    apply prod.hom_ext <;>
      simp only [Category.assoc, prod.lift_fst, prod.lift_snd,
        prodIsoPullback_inv_fst, prodIsoPullback_inv_snd, e, pullback.congrHom_hom,
        pullback.map, pullback.mapDesc, pullback.lift_fst, pullback.lift_snd, Category.comp_id]
  rw [he]
  infer_instance

theorem pair_of_closed {S X Y Z : Scheme.{u}} [S.IsSeparated]
    (f : X ⟶ S) (g : Y ⟶ S) (c : Z ⟶ pullback f g) [IsClosedImmersion c] :
    IsClosedImmersion (prod.lift (c ≫ pullback.fst f g) (c ≫ pullback.snd f g)) := by
  have := closed f g
  rw [← prod.comp_lift]
  infer_instance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.Embedding.PullbackEmbedding
