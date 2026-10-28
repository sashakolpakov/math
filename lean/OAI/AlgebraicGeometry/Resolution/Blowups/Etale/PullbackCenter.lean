import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.EtaleBoundary
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.Nonzero

/-! # Pullback Center -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Etale.PullbackCenter.Construction

noncomputable section

/-! Actual smooth centers and nonzero ideals persist under nonempty étale pullback. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem idealSheaf_comap_nonempty_etale_ne_bot
    {V X : Scheme} [IsIntegral X] [Nonempty V] (q : V ⟶ X) [Etale q]
    (I : X.IdealSheafData) (hI : I ≠ ⊥) : I.comap q ≠ ⊥ := by
  let : IsDominant q := ⟨q.isOpenMap.isOpen_range.dense (Set.range_nonempty q)⟩
  let : IsSchemeTheoreticallyDominant q := IsSchemeTheoreticallyDominant.of_isDominant q
  exact GlobalBlowup.Nonzero.Construction.idealSheaf_comap_ne_bot_of_ker_eq_bot q q.ker_eq_bot I hI

theorem idealSheaf_comap_etale_smooth_center
    {V X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (q : V ⟶ X) [Etale q]
    (I : X.IdealSheafData) [Smooth (I.subschemeι ≫ f)] :
    Smooth ((I.comap q).subschemeι ≫ (q ≫ f)) := by
  rw [← I.comapIso_hom_fst q, Category.assoc, ← Category.assoc (pullback.fst q I.subschemeι),
    pullback.condition, Category.assoc]
  infer_instance

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Etale.PullbackCenter.Construction
