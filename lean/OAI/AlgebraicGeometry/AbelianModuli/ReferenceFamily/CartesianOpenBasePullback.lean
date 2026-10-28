import Mathlib.AlgebraicGeometry.Restrict

/-! # Cartesian Open Base Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CartesianOpenBasePullback

noncomputable section

/-! A cartesian family whose base map factors through an open has a
constructed cartesian factorization through the actual open base change. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem cartesian_open_base_pullback_factor
    {X Y S T : Scheme.{0}} (f : X ⟶ S) (a : Y ⟶ X) (ρ : Y ⟶ T) (t : T ⟶ S)
    (hp : IsPullback a ρ f t) (U : S.Opens) (k : T ⟶ U.toScheme) (hk : k ≫ U.ι = t) :
    ∃ b : Y ⟶ pullback f U.ι, b ≫ pullback.fst f U.ι = a ∧
      IsPullback b ρ (pullback.snd f U.ι) k := by
  have hw : a ≫ f = (ρ ≫ k) ≫ U.ι := by
    rw [Category.assoc, hk]
    exact hp.w
  let b := pullback.lift a (ρ ≫ k) hw
  have hb : b ≫ pullback.fst f U.ι = a := pullback.lift_fst _ _ _
  have hc : b ≫ pullback.snd f U.ι = ρ ≫ k := pullback.lift_snd _ _ _
  have hout : IsPullback (b ≫ pullback.fst f U.ι) ρ f (k ≫ U.ι) := by
    rw [hb, hk]
    exact hp
  exact ⟨b, hb, hout.of_right hc (IsPullback.of_hasPullback f U.ι)⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CartesianOpenBasePullback
