import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Pullback Vanishing -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Ideal.PullbackVanishing

noncomputable section

/-! Vanishing of an ideal is unchanged by an isomorphism or by
reassociating an iterated base change. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem ideal_comap_iso_eq_bot_iff {X Y : Scheme.{u}} (e : X ≅ Y)
    (K : Y.IdealSheafData) : K.comap e.hom = ⊥ ↔ K = ⊥ := by
  constructor
  · intro h
    have he := congrArg (fun J : X.IdealSheafData => J.comap e.inv) h
    simpa only [← Scheme.IdealSheafData.comap_comp, Iso.inv_hom_id,
      Scheme.IdealSheafData.comap_id, Scheme.IdealSheafData.comap_bot] using he
  · intro h
    rw [h, Scheme.IdealSheafData.comap_bot]

theorem pullback_ideal_vanishing_comp {X S T U : Scheme.{u}}
    (f : X ⟶ S) (g : T ⟶ S) (h : U ⟶ T) (K : X.IdealSheafData) :
    (K.comap (pullback.fst f g)).comap (pullback.fst (pullback.snd f g) h) = ⊥ ↔
      K.comap (pullback.fst f (h ≫ g)) = ⊥ := by
  let e := pullbackLeftPullbackSndIso f g h
  rw [← Scheme.IdealSheafData.comap_comp,
    ← pullbackLeftPullbackSndIso_hom_fst, Scheme.IdealSheafData.comap_comp]
  exact ideal_comap_iso_eq_bot_iff e _

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Ideal.PullbackVanishing
