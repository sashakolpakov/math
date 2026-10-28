import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.SmoothBaseOpen
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FactoredBaseRecovery

/-! # Base Open Factorization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.BaseOpenFactorization

noncomputable section

/-! Any Cartesian base change landing in an open base where the restricted family is smooth is itself smooth. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem smooth_pullback_of_smooth_restriction
    {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Opens) [Smooth (f ∣_ U)] :
    Smooth (pullback.snd f U.ι) := by
  let h := (isPullback_morphismRestrict f U).flip
  have : Smooth h.isoPullback.inv := inferInstance
  have hh : Smooth (h.isoPullback.inv ≫ (f ∣_ U)) := AlgebraicGeometry.smooth_comp _ _
  exact (congrArg Smooth h.isoPullback_inv_snd).mp hh

theorem smooth_recovery_of_range_subset_open
    {X Y S T : Scheme.{u}} (q : Y ⟶ X) (p : Y ⟶ T) (f : X ⟶ S) (c : T ⟶ S)
    (h : IsPullback q p f c) (U : S.Opens) [Smooth (f ∣_ U)] (hc : Set.range c ⊆ U) : Smooth p := by
  let a : T ⟶ U.toScheme := IsOpenImmersion.lift U.ι c (by simpa only [Scheme.Opens.range_ι] using hc)
  have ha : a ≫ U.ι = c := IsOpenImmersion.lift_fac _ _ _
  have H : IsPullback q p f (a ≫ U.ι) := by
    rw [ha]
    exact h
  have hs : Smooth (pullback.snd f U.ι) := smooth_pullback_of_smooth_restriction f U
  exact MorphismProperty.of_isPullback (P := @Smooth) (FactoredBaseRecovery.factoredBaseRecovery_isPullback q p f a U.ι H) hs

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.BaseOpenFactorization
